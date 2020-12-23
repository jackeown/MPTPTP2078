%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GTUoeMxK2v

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:19 EST 2020

% Result     : Theorem 33.02s
% Output     : Refutation 33.02s
% Verified   : 
% Statistics : Number of formulae       :  510 (28963 expanded)
%              Number of leaves         :   55 (8999 expanded)
%              Depth                    :   42
%              Number of atoms          : 4799 (548941 expanded)
%              Number of equality atoms :  324 (36276 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
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

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('14',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('16',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['17','22'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X10 ) )
      = ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('25',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('30',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('31',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('35',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k6_partfun1 @ X1 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('42',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['23','44'])).

thf('46',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['17','22'])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('48',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('50',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('52',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('54',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('64',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('66',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('71',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('72',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','75'])).

thf('77',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('78',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('79',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('86',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('87',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('88',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('96',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('97',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('98',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('99',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','99'])).

thf('101',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('103',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('107',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('110',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('111',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','111'])).

thf('113',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('114',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('115',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('116',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('117',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['115','116'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('118',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('119',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('121',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('122',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('123',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('125',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('126',plain,(
    v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('128',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('129',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('131',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('132',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('133',plain,(
    v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['119','120','126','133'])).

thf('135',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('136',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('137',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('142',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['134','141'])).

thf('143',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('144',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('146',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['114','146'])).

thf('148',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('149',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) @ sk_C )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( sk_C
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['113','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('152',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','153'])).

thf('155',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['50','156'])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['49','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('160',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138','139','140'])).

thf('162',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('164',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('166',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('168',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['165','168'])).

thf('170',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['169','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('174',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','171','174'])).

thf('176',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','175'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('177',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X22
        = ( k2_funct_1 @ X23 ) )
      | ( ( k5_relat_1 @ X22 @ X23 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X23 ) ) )
      | ( ( k2_relat_1 @ X22 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('178',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('179',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X22
        = ( k2_funct_1 @ X23 ) )
      | ( ( k5_relat_1 @ X22 @ X23 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
      | ( ( k2_relat_1 @ X22 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) )
       != ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['176','179'])).

thf('181',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('182',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('183',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('184',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('185',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('186',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('187',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('189',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('190',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('191',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['184','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('194',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('196',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('197',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) )
       != ( k6_partfun1 @ sk_A ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ sk_C ) )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','194','197'])).

thf('199',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('200',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X56 @ X55 @ X54 )
       != X55 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X56 @ X55 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('201',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('205',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206'])).

thf('208',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('210',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('212',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X56 @ X55 @ X54 )
       != X55 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X54 ) @ X55 @ X56 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X56 @ X55 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('215',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('219',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['215','216','217','218','219','220'])).

thf('222',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('224',plain,
    ( ~ ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('226',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('227',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('228',plain,
    ( ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['225','228'])).

thf('230',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    zip_tseitin_1 @ ( k4_relat_1 @ sk_C ) @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['229','230'])).

thf('232',plain,
    ( sk_B
    = ( k1_relset_1 @ sk_B @ sk_A @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['224','231'])).

thf('233',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['212','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) )
       != ( k6_partfun1 @ sk_A ) )
      | ( ( k2_relat_1 @ X0 )
       != sk_B )
      | ( X0 = sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['198','233'])).

thf('235',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['160','234'])).

thf('236',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('237',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('238',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('239',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['237','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('246',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('247',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('248',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('249',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('252',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['247','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['246','253'])).

thf('255',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('258',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('259',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('260',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('261',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['258','261'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k4_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['257','263'])).

thf('265',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('266',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['264','265','266'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['256','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['245','271'])).

thf('273',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['272','273'])).

thf('275',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['244','274'])).

thf('276',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('277',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('278',plain,(
    v1_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['275','276','277'])).

thf('279',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['236','278'])).

thf('280',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['17','22'])).

thf('281',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('282',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('283',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['235','282'])).

thf('284',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('287',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( ( k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50 )
        = ( k5_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('288',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['285','290'])).

thf('292',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('294',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['284','293'])).

thf('295',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('297',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('298',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['296','297'])).

thf('299',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['298','299'])).

thf('301',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['295','300'])).

thf('302',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('304',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['301','302','303'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('305',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('306',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['294','306'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('308',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('309',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['307','308'])).

thf('310',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('311',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['283','309','310'])).

thf('312',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('314',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('315',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['313','314'])).

thf('316',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('317',plain,
    ( ( ( k2_funct_1 @ sk_D )
      = ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['315','316'])).

thf('318',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('319',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('320',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('321',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('322',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['320','321'])).

thf('323',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('324',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['322','323'])).

thf('325',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['319','324'])).

thf('326',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('327',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['325','326'])).

thf('328',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('329',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference(clc,[status(thm)],['327','328'])).

thf('330',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['318','329'])).

thf('331',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) )
        = ( k5_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('333',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('334',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('335',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['333','334'])).

thf('336',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('337',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['335','336'])).

thf('338',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['332','337'])).

thf('339',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('340',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['338','339'])).

thf('341',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('342',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['340','341'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('343',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X17 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('344',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
       != ( k1_relat_1 @ sk_D ) )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['342','343'])).

thf('345',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('346',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('348',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ sk_D ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
       != sk_B )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['344','345','346','347'])).

thf('349',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
     != sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['331','348'])).

thf('350',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('351',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('352',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('353',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('354',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,
    ( sk_C
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('356',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['212','232'])).

thf('357',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('358',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['349','350','351','352','353','354','355','356','357'])).

thf('359',plain,
    ( ( v2_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['358'])).

thf('360',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['307','308'])).

thf('361',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('362',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('363',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['361','362'])).

thf('364',plain,(
    v2_funct_1 @ sk_D ),
    inference(demod,[status(thm)],['359','360','363'])).

thf('365',plain,
    ( ( k2_funct_1 @ sk_D )
    = ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['317','364'])).

thf('366',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('367',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['365','366'])).

thf('368',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('369',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('370',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,(
    v2_funct_1 @ sk_D ),
    inference(demod,[status(thm)],['359','360','363'])).

thf('372',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['367','368','369','370','371'])).

thf('373',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('374',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('375',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ X19 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('376',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('377',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('378',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('379',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k1_relat_1 @ X19 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('380',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('381',plain,(
    ! [X53: $i] :
      ( ( k6_partfun1 @ X53 )
      = ( k6_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('382',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['380','381'])).

thf('383',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X22
        = ( k2_funct_1 @ X23 ) )
      | ( ( k5_relat_1 @ X22 @ X23 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
      | ( ( k2_relat_1 @ X22 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('384',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['382','383'])).

thf('385',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['384'])).

thf('386',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['379','385'])).

thf('387',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['386'])).

thf('388',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['378','387'])).

thf('389',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['388'])).

thf('390',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['377','389'])).

thf('391',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['390'])).

thf('392',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['376','391'])).

thf('393',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['392'])).

thf('394',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['375','393'])).

thf('395',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['394'])).

thf('396',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('397',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('398',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('399',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('400',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('401',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('402',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('403',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('404',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('405',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('406',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('407',plain,(
    ! [X16: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('408',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['406','407'])).

thf('409',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['405','408'])).

thf('410',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['409'])).

thf('411',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['404','410'])).

thf('412',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['411'])).

thf('413',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['403','412'])).

thf('414',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['413'])).

thf('415',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('416',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('417',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['415','416'])).

thf('418',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['414','417'])).

thf('419',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['418'])).

thf('420',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['402','419'])).

thf('421',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['420'])).

thf('422',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['401','421'])).

thf('423',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['422'])).

thf('424',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('425',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['423','424'])).

thf('426',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['400','425'])).

thf('427',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['426'])).

thf('428',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['399','427'])).

thf('429',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['398','428'])).

thf('430',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['429'])).

thf('431',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['397','430'])).

thf('432',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['431'])).

thf('433',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['396','432'])).

thf('434',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['433'])).

thf('435',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['395','434'])).

thf('436',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['435'])).

thf('437',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['374','436'])).

thf('438',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['373','437'])).

thf('439',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('440',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('441',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('442',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('443',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['279','280','281'])).

thf('444',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['438','439','440','441','442','443'])).

thf('445',plain,(
    v2_funct_1 @ sk_D ),
    inference(demod,[status(thm)],['359','360','363'])).

thf('446',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['444','445'])).

thf('447',plain,
    ( ( sk_B != sk_B )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C ) ),
    inference(demod,[status(thm)],['312','372','446'])).

thf('448',plain,
    ( ( k4_relat_1 @ sk_D )
    = sk_C ),
    inference(simplify,[status(thm)],['447'])).

thf('449',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['48','448'])).

thf('450',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('451',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','60','61'])).

thf('452',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['450','451'])).

thf('453',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['449','452'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GTUoeMxK2v
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:05:48 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 33.02/33.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 33.02/33.21  % Solved by: fo/fo7.sh
% 33.02/33.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 33.02/33.21  % done 8898 iterations in 32.758s
% 33.02/33.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 33.02/33.21  % SZS output start Refutation
% 33.02/33.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 33.02/33.21  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 33.02/33.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 33.02/33.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 33.02/33.21  thf(sk_A_type, type, sk_A: $i).
% 33.02/33.21  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 33.02/33.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 33.02/33.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 33.02/33.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 33.02/33.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 33.02/33.21  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 33.02/33.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 33.02/33.21  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 33.02/33.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 33.02/33.21  thf(sk_C_type, type, sk_C: $i).
% 33.02/33.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 33.02/33.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 33.02/33.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 33.02/33.21  thf(sk_D_type, type, sk_D: $i).
% 33.02/33.21  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 33.02/33.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 33.02/33.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 33.02/33.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 33.02/33.21  thf(sk_B_type, type, sk_B: $i).
% 33.02/33.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 33.02/33.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 33.02/33.21  thf(t36_funct_2, conjecture,
% 33.02/33.21    (![A:$i,B:$i,C:$i]:
% 33.02/33.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 33.02/33.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 33.02/33.21       ( ![D:$i]:
% 33.02/33.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 33.02/33.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 33.02/33.21           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 33.02/33.21               ( r2_relset_1 @
% 33.02/33.21                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 33.02/33.21                 ( k6_partfun1 @ A ) ) & 
% 33.02/33.21               ( v2_funct_1 @ C ) ) =>
% 33.02/33.21             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 33.02/33.21               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 33.02/33.21  thf(zf_stmt_0, negated_conjecture,
% 33.02/33.21    (~( ![A:$i,B:$i,C:$i]:
% 33.02/33.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 33.02/33.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 33.02/33.21          ( ![D:$i]:
% 33.02/33.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 33.02/33.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 33.02/33.21              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 33.02/33.21                  ( r2_relset_1 @
% 33.02/33.21                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 33.02/33.21                    ( k6_partfun1 @ A ) ) & 
% 33.02/33.21                  ( v2_funct_1 @ C ) ) =>
% 33.02/33.21                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 33.02/33.21                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 33.02/33.21    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 33.02/33.21  thf('0', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf(d1_funct_2, axiom,
% 33.02/33.21    (![A:$i,B:$i,C:$i]:
% 33.02/33.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.02/33.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 33.02/33.21           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 33.02/33.21             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 33.02/33.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 33.02/33.21           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 33.02/33.21             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 33.02/33.21  thf(zf_stmt_1, axiom,
% 33.02/33.21    (![C:$i,B:$i,A:$i]:
% 33.02/33.21     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 33.02/33.21       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 33.02/33.21  thf('1', plain,
% 33.02/33.21      (![X33 : $i, X34 : $i, X35 : $i]:
% 33.02/33.21         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 33.02/33.21          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 33.02/33.21          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 33.02/33.21  thf('2', plain,
% 33.02/33.21      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 33.02/33.21        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 33.02/33.21      inference('sup-', [status(thm)], ['0', '1'])).
% 33.02/33.21  thf(zf_stmt_2, axiom,
% 33.02/33.21    (![B:$i,A:$i]:
% 33.02/33.21     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 33.02/33.21       ( zip_tseitin_0 @ B @ A ) ))).
% 33.02/33.21  thf('3', plain,
% 33.02/33.21      (![X31 : $i, X32 : $i]:
% 33.02/33.21         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_2])).
% 33.02/33.21  thf('4', plain,
% 33.02/33.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 33.02/33.21  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 33.02/33.21  thf(zf_stmt_5, axiom,
% 33.02/33.21    (![A:$i,B:$i,C:$i]:
% 33.02/33.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.02/33.21       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 33.02/33.21         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 33.02/33.21           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 33.02/33.21             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 33.02/33.21  thf('5', plain,
% 33.02/33.21      (![X36 : $i, X37 : $i, X38 : $i]:
% 33.02/33.21         (~ (zip_tseitin_0 @ X36 @ X37)
% 33.02/33.21          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 33.02/33.21          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 33.02/33.21  thf('6', plain,
% 33.02/33.21      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 33.02/33.21      inference('sup-', [status(thm)], ['4', '5'])).
% 33.02/33.21  thf('7', plain,
% 33.02/33.21      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 33.02/33.21      inference('sup-', [status(thm)], ['3', '6'])).
% 33.02/33.21  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf('9', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 33.02/33.21      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 33.02/33.21  thf('10', plain,
% 33.02/33.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf(redefinition_k1_relset_1, axiom,
% 33.02/33.21    (![A:$i,B:$i,C:$i]:
% 33.02/33.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 33.02/33.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 33.02/33.21  thf('11', plain,
% 33.02/33.21      (![X24 : $i, X25 : $i, X26 : $i]:
% 33.02/33.21         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 33.02/33.21          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 33.02/33.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 33.02/33.21  thf('12', plain,
% 33.02/33.21      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 33.02/33.21      inference('sup-', [status(thm)], ['10', '11'])).
% 33.02/33.21  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 33.02/33.21      inference('demod', [status(thm)], ['2', '9', '12'])).
% 33.02/33.21  thf(t78_relat_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( v1_relat_1 @ A ) =>
% 33.02/33.21       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 33.02/33.21  thf('14', plain,
% 33.02/33.21      (![X11 : $i]:
% 33.02/33.21         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 33.02/33.21          | ~ (v1_relat_1 @ X11))),
% 33.02/33.21      inference('cnf', [status(esa)], [t78_relat_1])).
% 33.02/33.21  thf(redefinition_k6_partfun1, axiom,
% 33.02/33.21    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 33.02/33.21  thf('15', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 33.02/33.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.02/33.21  thf('16', plain,
% 33.02/33.21      (![X11 : $i]:
% 33.02/33.21         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 33.02/33.21          | ~ (v1_relat_1 @ X11))),
% 33.02/33.21      inference('demod', [status(thm)], ['14', '15'])).
% 33.02/33.21  thf('17', plain,
% 33.02/33.21      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 33.02/33.21        | ~ (v1_relat_1 @ sk_D))),
% 33.02/33.21      inference('sup+', [status(thm)], ['13', '16'])).
% 33.02/33.21  thf('18', plain,
% 33.02/33.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf(cc2_relat_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( v1_relat_1 @ A ) =>
% 33.02/33.21       ( ![B:$i]:
% 33.02/33.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 33.02/33.21  thf('19', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 33.02/33.21          | (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X1))),
% 33.02/33.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 33.02/33.21  thf('20', plain,
% 33.02/33.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 33.02/33.21      inference('sup-', [status(thm)], ['18', '19'])).
% 33.02/33.21  thf(fc6_relat_1, axiom,
% 33.02/33.21    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 33.02/33.21  thf('21', plain,
% 33.02/33.21      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 33.02/33.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 33.02/33.21  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.21      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.21  thf('23', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 33.02/33.21      inference('demod', [status(thm)], ['17', '22'])).
% 33.02/33.21  thf(t72_relat_1, axiom,
% 33.02/33.21    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 33.02/33.21  thf('24', plain,
% 33.02/33.21      (![X10 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X10)) = (k6_relat_1 @ X10))),
% 33.02/33.21      inference('cnf', [status(esa)], [t72_relat_1])).
% 33.02/33.21  thf('25', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 33.02/33.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.02/33.21  thf('26', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 33.02/33.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.02/33.21  thf('27', plain,
% 33.02/33.21      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 33.02/33.21      inference('demod', [status(thm)], ['24', '25', '26'])).
% 33.02/33.21  thf(t54_relat_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( v1_relat_1 @ A ) =>
% 33.02/33.21       ( ![B:$i]:
% 33.02/33.21         ( ( v1_relat_1 @ B ) =>
% 33.02/33.21           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 33.02/33.21             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 33.02/33.21  thf('28', plain,
% 33.02/33.21      (![X6 : $i, X7 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X6)
% 33.02/33.21          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.21              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.21          | ~ (v1_relat_1 @ X7))),
% 33.02/33.21      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.21  thf('29', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 33.02/33.21            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 33.02/33.21          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 33.02/33.21          | ~ (v1_relat_1 @ X1))),
% 33.02/33.21      inference('sup+', [status(thm)], ['27', '28'])).
% 33.02/33.21  thf(fc4_funct_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 33.02/33.21       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 33.02/33.21  thf('30', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 33.02/33.21      inference('cnf', [status(esa)], [fc4_funct_1])).
% 33.02/33.21  thf('31', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 33.02/33.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.02/33.21  thf('32', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 33.02/33.21      inference('demod', [status(thm)], ['30', '31'])).
% 33.02/33.21  thf('33', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 33.02/33.21            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 33.02/33.21          | ~ (v1_relat_1 @ X1))),
% 33.02/33.21      inference('demod', [status(thm)], ['29', '32'])).
% 33.02/33.21  thf(dt_k4_relat_1, axiom,
% 33.02/33.21    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 33.02/33.21  thf('34', plain,
% 33.02/33.21      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.21      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.21  thf(involutiveness_k4_relat_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 33.02/33.21  thf('35', plain,
% 33.02/33.21      (![X5 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.21      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.21  thf('36', plain,
% 33.02/33.21      (![X6 : $i, X7 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X6)
% 33.02/33.21          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.21              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.21          | ~ (v1_relat_1 @ X7))),
% 33.02/33.21      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.21  thf('37', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 33.02/33.21            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 33.02/33.21          | ~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 33.02/33.21          | ~ (v1_relat_1 @ X1))),
% 33.02/33.21      inference('sup+', [status(thm)], ['35', '36'])).
% 33.02/33.21  thf('38', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X1)
% 33.02/33.21          | ~ (v1_relat_1 @ X0)
% 33.02/33.21          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 33.02/33.21              = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0)))),
% 33.02/33.21      inference('sup-', [status(thm)], ['34', '37'])).
% 33.02/33.21  thf('39', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 33.02/33.21            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 33.02/33.21          | ~ (v1_relat_1 @ X1)
% 33.02/33.21          | ~ (v1_relat_1 @ X0))),
% 33.02/33.21      inference('simplify', [status(thm)], ['38'])).
% 33.02/33.21  thf('40', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 33.02/33.21            = (k5_relat_1 @ (k4_relat_1 @ (k6_partfun1 @ X1)) @ X0))
% 33.02/33.21          | ~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ (k6_partfun1 @ X1)))),
% 33.02/33.21      inference('sup+', [status(thm)], ['33', '39'])).
% 33.02/33.21  thf('41', plain,
% 33.02/33.21      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 33.02/33.21      inference('demod', [status(thm)], ['24', '25', '26'])).
% 33.02/33.21  thf('42', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 33.02/33.21      inference('demod', [status(thm)], ['30', '31'])).
% 33.02/33.21  thf('43', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 33.02/33.21            = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 33.02/33.21          | ~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X0))),
% 33.02/33.21      inference('demod', [status(thm)], ['40', '41', '42'])).
% 33.02/33.21  thf('44', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X0)
% 33.02/33.21          | ((k4_relat_1 @ 
% 33.02/33.21              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 33.02/33.21              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 33.02/33.21      inference('simplify', [status(thm)], ['43'])).
% 33.02/33.21  thf('45', plain,
% 33.02/33.21      ((((k4_relat_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.21          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))
% 33.02/33.21        | ~ (v1_relat_1 @ sk_D))),
% 33.02/33.21      inference('sup+', [status(thm)], ['23', '44'])).
% 33.02/33.21  thf('46', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 33.02/33.21      inference('demod', [status(thm)], ['17', '22'])).
% 33.02/33.21  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.21      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.21  thf('48', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 33.02/33.21      inference('demod', [status(thm)], ['45', '46', '47'])).
% 33.02/33.21  thf('49', plain,
% 33.02/33.21      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.21      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.21  thf('50', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 33.02/33.21      inference('demod', [status(thm)], ['45', '46', '47'])).
% 33.02/33.21  thf('51', plain,
% 33.02/33.21      (![X5 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.21      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.21  thf('52', plain,
% 33.02/33.21      (![X5 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.21      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.21  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf(d9_funct_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 33.02/33.21       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 33.02/33.21  thf('54', plain,
% 33.02/33.21      (![X12 : $i]:
% 33.02/33.21         (~ (v2_funct_1 @ X12)
% 33.02/33.21          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 33.02/33.21          | ~ (v1_funct_1 @ X12)
% 33.02/33.21          | ~ (v1_relat_1 @ X12))),
% 33.02/33.21      inference('cnf', [status(esa)], [d9_funct_1])).
% 33.02/33.21  thf('55', plain,
% 33.02/33.21      ((~ (v1_relat_1 @ sk_C)
% 33.02/33.21        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 33.02/33.21        | ~ (v2_funct_1 @ sk_C))),
% 33.02/33.21      inference('sup-', [status(thm)], ['53', '54'])).
% 33.02/33.21  thf('56', plain,
% 33.02/33.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf('57', plain,
% 33.02/33.21      (![X0 : $i, X1 : $i]:
% 33.02/33.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 33.02/33.21          | (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X1))),
% 33.02/33.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 33.02/33.21  thf('58', plain,
% 33.02/33.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 33.02/33.21      inference('sup-', [status(thm)], ['56', '57'])).
% 33.02/33.21  thf('59', plain,
% 33.02/33.21      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 33.02/33.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 33.02/33.21  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.21      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.21  thf('61', plain, ((v2_funct_1 @ sk_C)),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf('62', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.21  thf(dt_k2_funct_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 33.02/33.21       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 33.02/33.21         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 33.02/33.21  thf('63', plain,
% 33.02/33.21      (![X13 : $i]:
% 33.02/33.21         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.21          | ~ (v1_funct_1 @ X13)
% 33.02/33.21          | ~ (v1_relat_1 @ X13))),
% 33.02/33.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.21  thf('64', plain,
% 33.02/33.21      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21        | ~ (v1_relat_1 @ sk_C)
% 33.02/33.21        | ~ (v1_funct_1 @ sk_C))),
% 33.02/33.21      inference('sup+', [status(thm)], ['62', '63'])).
% 33.02/33.21  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.21      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.21  thf('66', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf('67', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['64', '65', '66'])).
% 33.02/33.21  thf('68', plain,
% 33.02/33.21      (![X12 : $i]:
% 33.02/33.21         (~ (v2_funct_1 @ X12)
% 33.02/33.21          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 33.02/33.21          | ~ (v1_funct_1 @ X12)
% 33.02/33.21          | ~ (v1_relat_1 @ X12))),
% 33.02/33.21      inference('cnf', [status(esa)], [d9_funct_1])).
% 33.02/33.21  thf('69', plain,
% 33.02/33.21      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21        | ((k2_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21            = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.21        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('sup-', [status(thm)], ['67', '68'])).
% 33.02/33.21  thf('70', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.21  thf('71', plain,
% 33.02/33.21      (![X13 : $i]:
% 33.02/33.21         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 33.02/33.21          | ~ (v1_funct_1 @ X13)
% 33.02/33.21          | ~ (v1_relat_1 @ X13))),
% 33.02/33.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.21  thf('72', plain,
% 33.02/33.21      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21        | ~ (v1_relat_1 @ sk_C)
% 33.02/33.21        | ~ (v1_funct_1 @ sk_C))),
% 33.02/33.21      inference('sup+', [status(thm)], ['70', '71'])).
% 33.02/33.21  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.21      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.21  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf('75', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.21  thf('76', plain,
% 33.02/33.21      ((((k2_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21          = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.21        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('demod', [status(thm)], ['69', '75'])).
% 33.02/33.21  thf('77', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.21  thf(fc6_funct_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 33.02/33.21       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 33.02/33.21         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 33.02/33.21         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 33.02/33.21  thf('78', plain,
% 33.02/33.21      (![X16 : $i]:
% 33.02/33.21         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 33.02/33.21          | ~ (v2_funct_1 @ X16)
% 33.02/33.21          | ~ (v1_funct_1 @ X16)
% 33.02/33.21          | ~ (v1_relat_1 @ X16))),
% 33.02/33.21      inference('cnf', [status(esa)], [fc6_funct_1])).
% 33.02/33.21  thf('79', plain,
% 33.02/33.21      (((v2_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21        | ~ (v1_relat_1 @ sk_C)
% 33.02/33.21        | ~ (v1_funct_1 @ sk_C)
% 33.02/33.21        | ~ (v2_funct_1 @ sk_C))),
% 33.02/33.21      inference('sup+', [status(thm)], ['77', '78'])).
% 33.02/33.21  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.21      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.21  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 33.02/33.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.21  thf('83', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 33.02/33.21  thf('84', plain,
% 33.02/33.21      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('demod', [status(thm)], ['76', '83'])).
% 33.02/33.21  thf('85', plain,
% 33.02/33.21      (![X16 : $i]:
% 33.02/33.21         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 33.02/33.21          | ~ (v2_funct_1 @ X16)
% 33.02/33.21          | ~ (v1_funct_1 @ X16)
% 33.02/33.21          | ~ (v1_relat_1 @ X16))),
% 33.02/33.21      inference('cnf', [status(esa)], [fc6_funct_1])).
% 33.02/33.21  thf('86', plain,
% 33.02/33.21      (![X13 : $i]:
% 33.02/33.21         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 33.02/33.21          | ~ (v1_funct_1 @ X13)
% 33.02/33.21          | ~ (v1_relat_1 @ X13))),
% 33.02/33.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.21  thf('87', plain,
% 33.02/33.21      (![X13 : $i]:
% 33.02/33.21         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.21          | ~ (v1_funct_1 @ X13)
% 33.02/33.21          | ~ (v1_relat_1 @ X13))),
% 33.02/33.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.21  thf('88', plain,
% 33.02/33.21      (![X12 : $i]:
% 33.02/33.21         (~ (v2_funct_1 @ X12)
% 33.02/33.21          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 33.02/33.21          | ~ (v1_funct_1 @ X12)
% 33.02/33.21          | ~ (v1_relat_1 @ X12))),
% 33.02/33.21      inference('cnf', [status(esa)], [d9_funct_1])).
% 33.02/33.21  thf('89', plain,
% 33.02/33.21      (![X0 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_funct_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.21          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.21              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 33.02/33.21      inference('sup-', [status(thm)], ['87', '88'])).
% 33.02/33.21  thf('90', plain,
% 33.02/33.21      (![X0 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_funct_1 @ X0)
% 33.02/33.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.21          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.21              = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.21          | ~ (v1_funct_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X0))),
% 33.02/33.21      inference('sup-', [status(thm)], ['86', '89'])).
% 33.02/33.21  thf('91', plain,
% 33.02/33.21      (![X0 : $i]:
% 33.02/33.21         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.21          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.21          | ~ (v1_funct_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X0))),
% 33.02/33.21      inference('simplify', [status(thm)], ['90'])).
% 33.02/33.21  thf('92', plain,
% 33.02/33.21      (![X0 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_funct_1 @ X0)
% 33.02/33.21          | ~ (v2_funct_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X0)
% 33.02/33.21          | ~ (v1_funct_1 @ X0)
% 33.02/33.21          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.21              = (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.21      inference('sup-', [status(thm)], ['85', '91'])).
% 33.02/33.21  thf('93', plain,
% 33.02/33.21      (![X0 : $i]:
% 33.02/33.21         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.21          | ~ (v2_funct_1 @ X0)
% 33.02/33.21          | ~ (v1_funct_1 @ X0)
% 33.02/33.21          | ~ (v1_relat_1 @ X0))),
% 33.02/33.21      inference('simplify', [status(thm)], ['92'])).
% 33.02/33.21  thf('94', plain,
% 33.02/33.21      ((((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.21          = (k4_relat_1 @ (k2_funct_1 @ (k4_relat_1 @ sk_C))))
% 33.02/33.21        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('sup+', [status(thm)], ['84', '93'])).
% 33.02/33.21  thf('95', plain,
% 33.02/33.21      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('demod', [status(thm)], ['76', '83'])).
% 33.02/33.21  thf('96', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.21  thf('97', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['64', '65', '66'])).
% 33.02/33.21  thf('98', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 33.02/33.21  thf('99', plain,
% 33.02/33.21      (((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.21         = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.21      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 33.02/33.21  thf('100', plain,
% 33.02/33.21      ((((k2_funct_1 @ sk_C)
% 33.02/33.21          = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))
% 33.02/33.21        | ~ (v1_relat_1 @ sk_C))),
% 33.02/33.21      inference('sup+', [status(thm)], ['52', '99'])).
% 33.02/33.21  thf('101', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.21  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.21      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.21  thf('103', plain,
% 33.02/33.21      (((k4_relat_1 @ sk_C) = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.21      inference('demod', [status(thm)], ['100', '101', '102'])).
% 33.02/33.21  thf('104', plain,
% 33.02/33.21      (![X6 : $i, X7 : $i]:
% 33.02/33.21         (~ (v1_relat_1 @ X6)
% 33.02/33.21          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.21              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.21          | ~ (v1_relat_1 @ X7))),
% 33.02/33.21      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.21  thf('105', plain,
% 33.02/33.21      (![X0 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ X0))
% 33.02/33.21            = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ sk_C)))
% 33.02/33.21          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.21          | ~ (v1_relat_1 @ X0))),
% 33.02/33.21      inference('sup+', [status(thm)], ['103', '104'])).
% 33.02/33.21  thf('106', plain,
% 33.02/33.21      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('demod', [status(thm)], ['76', '83'])).
% 33.02/33.21  thf('107', plain,
% 33.02/33.21      (![X13 : $i]:
% 33.02/33.21         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 33.02/33.21          | ~ (v1_funct_1 @ X13)
% 33.02/33.21          | ~ (v1_relat_1 @ X13))),
% 33.02/33.21      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.21  thf('108', plain,
% 33.02/33.21      (((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.21        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.21        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('sup+', [status(thm)], ['106', '107'])).
% 33.02/33.21  thf('109', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.21  thf('110', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['64', '65', '66'])).
% 33.02/33.21  thf('111', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.21      inference('demod', [status(thm)], ['108', '109', '110'])).
% 33.02/33.21  thf('112', plain,
% 33.02/33.21      (![X0 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ X0))
% 33.02/33.21            = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ sk_C)))
% 33.02/33.21          | ~ (v1_relat_1 @ X0))),
% 33.02/33.21      inference('demod', [status(thm)], ['105', '111'])).
% 33.02/33.21  thf('113', plain,
% 33.02/33.21      (![X11 : $i]:
% 33.02/33.21         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 33.02/33.21          | ~ (v1_relat_1 @ X11))),
% 33.02/33.21      inference('demod', [status(thm)], ['14', '15'])).
% 33.02/33.21  thf('114', plain,
% 33.02/33.21      (![X5 : $i]:
% 33.02/33.21         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.21      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.21  thf('115', plain,
% 33.02/33.21      (((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.21         = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.21      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 33.02/33.21  thf('116', plain,
% 33.02/33.21      (((k4_relat_1 @ sk_C) = (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.21      inference('demod', [status(thm)], ['100', '101', '102'])).
% 33.02/33.21  thf('117', plain,
% 33.02/33.21      (((k2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) = (k4_relat_1 @ sk_C))),
% 33.02/33.21      inference('demod', [status(thm)], ['115', '116'])).
% 33.02/33.21  thf(t55_funct_1, axiom,
% 33.02/33.21    (![A:$i]:
% 33.02/33.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 33.02/33.21       ( ( v2_funct_1 @ A ) =>
% 33.02/33.21         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 33.02/33.21           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 33.02/33.21  thf('118', plain,
% 33.02/33.21      (![X19 : $i]:
% 33.02/33.21         (~ (v2_funct_1 @ X19)
% 33.02/33.21          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 33.02/33.22          | ~ (v1_funct_1 @ X19)
% 33.02/33.22          | ~ (v1_relat_1 @ X19))),
% 33.02/33.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 33.02/33.22  thf('119', plain,
% 33.02/33.22      ((((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22          = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.22      inference('sup+', [status(thm)], ['117', '118'])).
% 33.02/33.22  thf('120', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['108', '109', '110'])).
% 33.02/33.22  thf('121', plain,
% 33.02/33.22      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['76', '83'])).
% 33.02/33.22  thf('122', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('123', plain,
% 33.02/33.22      (((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['121', '122'])).
% 33.02/33.22  thf('124', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.22  thf('125', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['64', '65', '66'])).
% 33.02/33.22  thf('126', plain, ((v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['123', '124', '125'])).
% 33.02/33.22  thf('127', plain,
% 33.02/33.22      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['76', '83'])).
% 33.02/33.22  thf('128', plain,
% 33.02/33.22      (![X16 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 33.02/33.22          | ~ (v2_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_relat_1 @ X16))),
% 33.02/33.22      inference('cnf', [status(esa)], [fc6_funct_1])).
% 33.02/33.22  thf('129', plain,
% 33.02/33.22      (((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['127', '128'])).
% 33.02/33.22  thf('130', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.22  thf('131', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['64', '65', '66'])).
% 33.02/33.22  thf('132', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 33.02/33.22  thf('133', plain, ((v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 33.02/33.22  thf('134', plain,
% 33.02/33.22      (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22         = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['119', '120', '126', '133'])).
% 33.02/33.22  thf('135', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.22  thf('136', plain,
% 33.02/33.22      (![X19 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X19)
% 33.02/33.22          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 33.02/33.22          | ~ (v1_funct_1 @ X19)
% 33.02/33.22          | ~ (v1_relat_1 @ X19))),
% 33.02/33.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 33.02/33.22  thf('137', plain,
% 33.02/33.22      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_relat_1 @ sk_C)
% 33.02/33.22        | ~ (v1_funct_1 @ sk_C)
% 33.02/33.22        | ~ (v2_funct_1 @ sk_C))),
% 33.02/33.22      inference('sup+', [status(thm)], ['135', '136'])).
% 33.02/33.22  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.22      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.22  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('141', plain,
% 33.02/33.22      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 33.02/33.22  thf('142', plain,
% 33.02/33.22      (((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) = (k1_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['134', '141'])).
% 33.02/33.22  thf('143', plain,
% 33.02/33.22      (![X11 : $i]:
% 33.02/33.22         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 33.02/33.22          | ~ (v1_relat_1 @ X11))),
% 33.02/33.22      inference('demod', [status(thm)], ['14', '15'])).
% 33.02/33.22  thf('144', plain,
% 33.02/33.22      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 33.02/33.22          (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22          = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.22      inference('sup+', [status(thm)], ['142', '143'])).
% 33.02/33.22  thf('145', plain, ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['108', '109', '110'])).
% 33.02/33.22  thf('146', plain,
% 33.02/33.22      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ 
% 33.02/33.22         (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22         = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['144', '145'])).
% 33.02/33.22  thf('147', plain,
% 33.02/33.22      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C)
% 33.02/33.22          = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_relat_1 @ sk_C))),
% 33.02/33.22      inference('sup+', [status(thm)], ['114', '146'])).
% 33.02/33.22  thf('148', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.22      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.22  thf('149', plain,
% 33.02/33.22      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)) @ sk_C)
% 33.02/33.22         = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['147', '148'])).
% 33.02/33.22  thf('150', plain,
% 33.02/33.22      ((((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C))) | ~ (v1_relat_1 @ sk_C))),
% 33.02/33.22      inference('sup+', [status(thm)], ['113', '149'])).
% 33.02/33.22  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.22      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.22  thf('152', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['150', '151'])).
% 33.02/33.22  thf('153', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ sk_C @ X0))
% 33.02/33.22            = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ sk_C)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('demod', [status(thm)], ['112', '152'])).
% 33.02/33.22  thf('154', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 33.02/33.22            = (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['51', '153'])).
% 33.02/33.22  thf('155', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('156', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 33.02/33.22              = (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.22      inference('clc', [status(thm)], ['154', '155'])).
% 33.02/33.22  thf('157', plain,
% 33.02/33.22      ((((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 33.02/33.22          = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['50', '156'])).
% 33.02/33.22  thf('158', plain,
% 33.02/33.22      ((~ (v1_relat_1 @ sk_D)
% 33.02/33.22        | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 33.02/33.22            = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['49', '157'])).
% 33.02/33.22  thf('159', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('160', plain,
% 33.02/33.22      (((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 33.02/33.22         = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['158', '159'])).
% 33.02/33.22  thf('161', plain,
% 33.02/33.22      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['137', '138', '139', '140'])).
% 33.02/33.22  thf('162', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('163', plain,
% 33.02/33.22      (![X33 : $i, X34 : $i, X35 : $i]:
% 33.02/33.22         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 33.02/33.22          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 33.02/33.22          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 33.02/33.22  thf('164', plain,
% 33.02/33.22      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 33.02/33.22        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['162', '163'])).
% 33.02/33.22  thf('165', plain,
% 33.02/33.22      (![X31 : $i, X32 : $i]:
% 33.02/33.22         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 33.02/33.22  thf('166', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('167', plain,
% 33.02/33.22      (![X36 : $i, X37 : $i, X38 : $i]:
% 33.02/33.22         (~ (zip_tseitin_0 @ X36 @ X37)
% 33.02/33.22          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 33.02/33.22          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_5])).
% 33.02/33.22  thf('168', plain,
% 33.02/33.22      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 33.02/33.22      inference('sup-', [status(thm)], ['166', '167'])).
% 33.02/33.22  thf('169', plain,
% 33.02/33.22      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 33.02/33.22      inference('sup-', [status(thm)], ['165', '168'])).
% 33.02/33.22  thf('170', plain, (((sk_B) != (k1_xboole_0))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('171', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 33.02/33.22      inference('simplify_reflect-', [status(thm)], ['169', '170'])).
% 33.02/33.22  thf('172', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('173', plain,
% 33.02/33.22      (![X24 : $i, X25 : $i, X26 : $i]:
% 33.02/33.22         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 33.02/33.22          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 33.02/33.22      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 33.02/33.22  thf('174', plain,
% 33.02/33.22      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 33.02/33.22      inference('sup-', [status(thm)], ['172', '173'])).
% 33.02/33.22  thf('175', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['164', '171', '174'])).
% 33.02/33.22  thf('176', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['161', '175'])).
% 33.02/33.22  thf(t64_funct_1, axiom,
% 33.02/33.22    (![A:$i]:
% 33.02/33.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 33.02/33.22       ( ![B:$i]:
% 33.02/33.22         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 33.02/33.22           ( ( ( v2_funct_1 @ A ) & 
% 33.02/33.22               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 33.02/33.22               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 33.02/33.22             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 33.02/33.22  thf('177', plain,
% 33.02/33.22      (![X22 : $i, X23 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X22)
% 33.02/33.22          | ~ (v1_funct_1 @ X22)
% 33.02/33.22          | ((X22) = (k2_funct_1 @ X23))
% 33.02/33.22          | ((k5_relat_1 @ X22 @ X23) != (k6_relat_1 @ (k2_relat_1 @ X23)))
% 33.02/33.22          | ((k2_relat_1 @ X22) != (k1_relat_1 @ X23))
% 33.02/33.22          | ~ (v2_funct_1 @ X23)
% 33.02/33.22          | ~ (v1_funct_1 @ X23)
% 33.02/33.22          | ~ (v1_relat_1 @ X23))),
% 33.02/33.22      inference('cnf', [status(esa)], [t64_funct_1])).
% 33.02/33.22  thf('178', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 33.02/33.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.02/33.22  thf('179', plain,
% 33.02/33.22      (![X22 : $i, X23 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X22)
% 33.02/33.22          | ~ (v1_funct_1 @ X22)
% 33.02/33.22          | ((X22) = (k2_funct_1 @ X23))
% 33.02/33.22          | ((k5_relat_1 @ X22 @ X23) != (k6_partfun1 @ (k2_relat_1 @ X23)))
% 33.02/33.22          | ((k2_relat_1 @ X22) != (k1_relat_1 @ X23))
% 33.02/33.22          | ~ (v2_funct_1 @ X23)
% 33.02/33.22          | ~ (v1_funct_1 @ X23)
% 33.02/33.22          | ~ (v1_relat_1 @ X23))),
% 33.02/33.22      inference('demod', [status(thm)], ['177', '178'])).
% 33.02/33.22  thf('180', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)) != (k6_partfun1 @ sk_A))
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22          | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22          | ((X0) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('sup-', [status(thm)], ['176', '179'])).
% 33.02/33.22  thf('181', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.22  thf('182', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['64', '65', '66'])).
% 33.02/33.22  thf('183', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 33.02/33.22  thf('184', plain,
% 33.02/33.22      (![X5 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.22      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.22  thf('185', plain,
% 33.02/33.22      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['76', '83'])).
% 33.02/33.22  thf('186', plain,
% 33.02/33.22      (![X19 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X19)
% 33.02/33.22          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 33.02/33.22          | ~ (v1_funct_1 @ X19)
% 33.02/33.22          | ~ (v1_relat_1 @ X19))),
% 33.02/33.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 33.02/33.22  thf('187', plain,
% 33.02/33.22      ((((k1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22          = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['185', '186'])).
% 33.02/33.22  thf('188', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.22  thf('189', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['64', '65', '66'])).
% 33.02/33.22  thf('190', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 33.02/33.22  thf('191', plain,
% 33.02/33.22      (((k1_relat_1 @ (k4_relat_1 @ sk_C))
% 33.02/33.22         = (k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))))),
% 33.02/33.22      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 33.02/33.22  thf('192', plain,
% 33.02/33.22      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 33.02/33.22        | ~ (v1_relat_1 @ sk_C))),
% 33.02/33.22      inference('sup+', [status(thm)], ['184', '191'])).
% 33.02/33.22  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.22      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.22  thf('194', plain,
% 33.02/33.22      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['192', '193'])).
% 33.02/33.22  thf('195', plain,
% 33.02/33.22      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['76', '83'])).
% 33.02/33.22  thf('196', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['150', '151'])).
% 33.02/33.22  thf('197', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['195', '196'])).
% 33.02/33.22  thf('198', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)) != (k6_partfun1 @ sk_A))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k2_relat_1 @ sk_C))
% 33.02/33.22          | ((X0) = (sk_C))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('demod', [status(thm)],
% 33.02/33.22                ['180', '181', '182', '183', '194', '197'])).
% 33.02/33.22  thf('199', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf(t31_funct_2, axiom,
% 33.02/33.22    (![A:$i,B:$i,C:$i]:
% 33.02/33.22     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 33.02/33.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 33.02/33.22       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 33.02/33.22         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 33.02/33.22           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 33.02/33.22           ( m1_subset_1 @
% 33.02/33.22             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 33.02/33.22  thf('200', plain,
% 33.02/33.22      (![X54 : $i, X55 : $i, X56 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X54)
% 33.02/33.22          | ((k2_relset_1 @ X56 @ X55 @ X54) != (X55))
% 33.02/33.22          | (m1_subset_1 @ (k2_funct_1 @ X54) @ 
% 33.02/33.22             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 33.02/33.22          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55)))
% 33.02/33.22          | ~ (v1_funct_2 @ X54 @ X56 @ X55)
% 33.02/33.22          | ~ (v1_funct_1 @ X54))),
% 33.02/33.22      inference('cnf', [status(esa)], [t31_funct_2])).
% 33.02/33.22  thf('201', plain,
% 33.02/33.22      ((~ (v1_funct_1 @ sk_C)
% 33.02/33.22        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 33.02/33.22        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 33.02/33.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 33.02/33.22        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 33.02/33.22        | ~ (v2_funct_1 @ sk_C))),
% 33.02/33.22      inference('sup-', [status(thm)], ['199', '200'])).
% 33.02/33.22  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('203', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('204', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.22  thf('205', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('206', plain, ((v2_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('207', plain,
% 33.02/33.22      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 33.02/33.22         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 33.02/33.22        | ((sk_B) != (sk_B)))),
% 33.02/33.22      inference('demod', [status(thm)],
% 33.02/33.22                ['201', '202', '203', '204', '205', '206'])).
% 33.02/33.22  thf('208', plain,
% 33.02/33.22      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 33.02/33.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['207'])).
% 33.02/33.22  thf('209', plain,
% 33.02/33.22      (![X24 : $i, X25 : $i, X26 : $i]:
% 33.02/33.22         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 33.02/33.22          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 33.02/33.22      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 33.02/33.22  thf('210', plain,
% 33.02/33.22      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))
% 33.02/33.22         = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['208', '209'])).
% 33.02/33.22  thf('211', plain,
% 33.02/33.22      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['192', '193'])).
% 33.02/33.22  thf('212', plain,
% 33.02/33.22      (((k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['210', '211'])).
% 33.02/33.22  thf('213', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('214', plain,
% 33.02/33.22      (![X54 : $i, X55 : $i, X56 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X54)
% 33.02/33.22          | ((k2_relset_1 @ X56 @ X55 @ X54) != (X55))
% 33.02/33.22          | (v1_funct_2 @ (k2_funct_1 @ X54) @ X55 @ X56)
% 33.02/33.22          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55)))
% 33.02/33.22          | ~ (v1_funct_2 @ X54 @ X56 @ X55)
% 33.02/33.22          | ~ (v1_funct_1 @ X54))),
% 33.02/33.22      inference('cnf', [status(esa)], [t31_funct_2])).
% 33.02/33.22  thf('215', plain,
% 33.02/33.22      ((~ (v1_funct_1 @ sk_C)
% 33.02/33.22        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 33.02/33.22        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 33.02/33.22        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 33.02/33.22        | ~ (v2_funct_1 @ sk_C))),
% 33.02/33.22      inference('sup-', [status(thm)], ['213', '214'])).
% 33.02/33.22  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('217', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('218', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.22  thf('219', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('220', plain, ((v2_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('221', plain,
% 33.02/33.22      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A) | ((sk_B) != (sk_B)))),
% 33.02/33.22      inference('demod', [status(thm)],
% 33.02/33.22                ['215', '216', '217', '218', '219', '220'])).
% 33.02/33.22  thf('222', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 33.02/33.22      inference('simplify', [status(thm)], ['221'])).
% 33.02/33.22  thf('223', plain,
% 33.02/33.22      (![X33 : $i, X34 : $i, X35 : $i]:
% 33.02/33.22         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 33.02/33.22          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 33.02/33.22          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_1])).
% 33.02/33.22  thf('224', plain,
% 33.02/33.22      ((~ (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 33.02/33.22        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['222', '223'])).
% 33.02/33.22  thf('225', plain,
% 33.02/33.22      (![X31 : $i, X32 : $i]:
% 33.02/33.22         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_2])).
% 33.02/33.22  thf('226', plain,
% 33.02/33.22      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 33.02/33.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['207'])).
% 33.02/33.22  thf('227', plain,
% 33.02/33.22      (![X36 : $i, X37 : $i, X38 : $i]:
% 33.02/33.22         (~ (zip_tseitin_0 @ X36 @ X37)
% 33.02/33.22          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 33.02/33.22          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_5])).
% 33.02/33.22  thf('228', plain,
% 33.02/33.22      (((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)
% 33.02/33.22        | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 33.02/33.22      inference('sup-', [status(thm)], ['226', '227'])).
% 33.02/33.22  thf('229', plain,
% 33.02/33.22      ((((sk_A) = (k1_xboole_0))
% 33.02/33.22        | (zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B))),
% 33.02/33.22      inference('sup-', [status(thm)], ['225', '228'])).
% 33.02/33.22  thf('230', plain, (((sk_A) != (k1_xboole_0))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('231', plain, ((zip_tseitin_1 @ (k4_relat_1 @ sk_C) @ sk_A @ sk_B)),
% 33.02/33.22      inference('simplify_reflect-', [status(thm)], ['229', '230'])).
% 33.02/33.22  thf('232', plain,
% 33.02/33.22      (((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['224', '231'])).
% 33.02/33.22  thf('233', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 33.02/33.22      inference('sup+', [status(thm)], ['212', '232'])).
% 33.02/33.22  thf('234', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)) != (k6_partfun1 @ sk_A))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (sk_B))
% 33.02/33.22          | ((X0) = (sk_C))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('demod', [status(thm)], ['198', '233'])).
% 33.02/33.22  thf('235', plain,
% 33.02/33.22      ((((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) != (k6_partfun1 @ sk_A))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.22        | ((k4_relat_1 @ sk_D) = (sk_C))
% 33.02/33.22        | ((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['160', '234'])).
% 33.02/33.22  thf('236', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 33.02/33.22            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X1))),
% 33.02/33.22      inference('demod', [status(thm)], ['29', '32'])).
% 33.02/33.22  thf('237', plain,
% 33.02/33.22      (![X11 : $i]:
% 33.02/33.22         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 33.02/33.22          | ~ (v1_relat_1 @ X11))),
% 33.02/33.22      inference('demod', [status(thm)], ['14', '15'])).
% 33.02/33.22  thf('238', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k4_relat_1 @ 
% 33.02/33.22              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 33.02/33.22              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['43'])).
% 33.02/33.22  thf('239', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('240', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ 
% 33.02/33.22               (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))))),
% 33.02/33.22      inference('sup+', [status(thm)], ['238', '239'])).
% 33.02/33.22  thf('241', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['237', '240'])).
% 33.02/33.22  thf('242', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['241'])).
% 33.02/33.22  thf('243', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('244', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 33.02/33.22      inference('clc', [status(thm)], ['242', '243'])).
% 33.02/33.22  thf('245', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('246', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('247', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['45', '46', '47'])).
% 33.02/33.22  thf('248', plain,
% 33.02/33.22      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 33.02/33.22      inference('demod', [status(thm)], ['24', '25', '26'])).
% 33.02/33.22  thf('249', plain,
% 33.02/33.22      (![X6 : $i, X7 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X6)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.22              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.22          | ~ (v1_relat_1 @ X7))),
% 33.02/33.22      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.22  thf('250', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 33.02/33.22            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['248', '249'])).
% 33.02/33.22  thf('251', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 33.02/33.22      inference('demod', [status(thm)], ['30', '31'])).
% 33.02/33.22  thf('252', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 33.02/33.22            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 33.02/33.22          | ~ (v1_relat_1 @ X1))),
% 33.02/33.22      inference('demod', [status(thm)], ['250', '251'])).
% 33.02/33.22  thf('253', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ 
% 33.02/33.22            (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ X0)))
% 33.02/33.22            = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['247', '252'])).
% 33.02/33.22  thf('254', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ sk_D)
% 33.02/33.22          | ((k4_relat_1 @ 
% 33.02/33.22              (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ X0)))
% 33.02/33.22              = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['246', '253'])).
% 33.02/33.22  thf('255', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('256', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ X0)))
% 33.02/33.22           = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['254', '255'])).
% 33.02/33.22  thf('257', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 33.02/33.22            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 33.02/33.22          | ~ (v1_relat_1 @ X1))),
% 33.02/33.22      inference('demod', [status(thm)], ['250', '251'])).
% 33.02/33.22  thf('258', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('259', plain,
% 33.02/33.22      (![X5 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.22      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.22  thf('260', plain,
% 33.02/33.22      (![X6 : $i, X7 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X6)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.22              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.22          | ~ (v1_relat_1 @ X7))),
% 33.02/33.22      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.22  thf('261', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 33.02/33.22            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['259', '260'])).
% 33.02/33.22  thf('262', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 33.02/33.22              = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['258', '261'])).
% 33.02/33.22  thf('263', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 33.02/33.22            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['262'])).
% 33.02/33.22  thf('264', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))))
% 33.02/33.22            = (k5_relat_1 @ X1 @ (k4_relat_1 @ (k6_partfun1 @ X0))))
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['257', '263'])).
% 33.02/33.22  thf('265', plain,
% 33.02/33.22      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 33.02/33.22      inference('demod', [status(thm)], ['24', '25', '26'])).
% 33.02/33.22  thf('266', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 33.02/33.22      inference('demod', [status(thm)], ['30', '31'])).
% 33.02/33.22  thf('267', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))))
% 33.02/33.22            = (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ X1))),
% 33.02/33.22      inference('demod', [status(thm)], ['264', '265', '266'])).
% 33.02/33.22  thf('268', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X1)
% 33.02/33.22          | ((k4_relat_1 @ 
% 33.02/33.22              (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))))
% 33.02/33.22              = (k5_relat_1 @ X1 @ (k6_partfun1 @ X0))))),
% 33.02/33.22      inference('simplify', [status(thm)], ['267'])).
% 33.02/33.22  thf('269', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('270', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X1)
% 33.02/33.22          | ~ (v1_relat_1 @ 
% 33.02/33.22               (k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))))),
% 33.02/33.22      inference('sup+', [status(thm)], ['268', '269'])).
% 33.02/33.22  thf('271', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.22          | (v1_relat_1 @ 
% 33.02/33.22             (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['256', '270'])).
% 33.02/33.22  thf('272', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ sk_D)
% 33.02/33.22          | (v1_relat_1 @ 
% 33.02/33.22             (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['245', '271'])).
% 33.02/33.22  thf('273', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('274', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D)))),
% 33.02/33.22      inference('demod', [status(thm)], ['272', '273'])).
% 33.02/33.22  thf('275', plain,
% 33.02/33.22      ((~ (v1_relat_1 @ sk_D)
% 33.02/33.22        | (v1_relat_1 @ 
% 33.02/33.22           (k5_relat_1 @ (k4_relat_1 @ sk_D) @ 
% 33.02/33.22            (k6_partfun1 @ (k1_relat_1 @ sk_D)))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['244', '274'])).
% 33.02/33.22  thf('276', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('277', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['2', '9', '12'])).
% 33.02/33.22  thf('278', plain,
% 33.02/33.22      ((v1_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k6_partfun1 @ sk_B)))),
% 33.02/33.22      inference('demod', [status(thm)], ['275', '276', '277'])).
% 33.02/33.22  thf('279', plain,
% 33.02/33.22      (((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)))
% 33.02/33.22        | ~ (v1_relat_1 @ sk_D))),
% 33.02/33.22      inference('sup+', [status(thm)], ['236', '278'])).
% 33.02/33.22  thf('280', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['17', '22'])).
% 33.02/33.22  thf('281', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('282', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['279', '280', '281'])).
% 33.02/33.22  thf('283', plain,
% 33.02/33.22      ((((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) != (k6_partfun1 @ sk_A))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.22        | ((k4_relat_1 @ sk_D) = (sk_C))
% 33.02/33.22        | ((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B)))),
% 33.02/33.22      inference('demod', [status(thm)], ['235', '282'])).
% 33.02/33.22  thf('284', plain,
% 33.02/33.22      ((r2_relset_1 @ sk_A @ sk_A @ 
% 33.02/33.22        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 33.02/33.22        (k6_partfun1 @ sk_A))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('285', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('286', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf(redefinition_k1_partfun1, axiom,
% 33.02/33.22    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 33.02/33.22     ( ( ( v1_funct_1 @ E ) & 
% 33.02/33.22         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 33.02/33.22         ( v1_funct_1 @ F ) & 
% 33.02/33.22         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 33.02/33.22       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 33.02/33.22  thf('287', plain,
% 33.02/33.22      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 33.02/33.22         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 33.02/33.22          | ~ (v1_funct_1 @ X47)
% 33.02/33.22          | ~ (v1_funct_1 @ X50)
% 33.02/33.22          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 33.02/33.22          | ((k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50)
% 33.02/33.22              = (k5_relat_1 @ X47 @ X50)))),
% 33.02/33.22      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 33.02/33.22  thf('288', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.02/33.22         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 33.02/33.22            = (k5_relat_1 @ sk_C @ X0))
% 33.02/33.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ sk_C))),
% 33.02/33.22      inference('sup-', [status(thm)], ['286', '287'])).
% 33.02/33.22  thf('289', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('290', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.02/33.22         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 33.02/33.22            = (k5_relat_1 @ sk_C @ X0))
% 33.02/33.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 33.02/33.22          | ~ (v1_funct_1 @ X0))),
% 33.02/33.22      inference('demod', [status(thm)], ['288', '289'])).
% 33.02/33.22  thf('291', plain,
% 33.02/33.22      ((~ (v1_funct_1 @ sk_D)
% 33.02/33.22        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 33.02/33.22            = (k5_relat_1 @ sk_C @ sk_D)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['285', '290'])).
% 33.02/33.22  thf('292', plain, ((v1_funct_1 @ sk_D)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('293', plain,
% 33.02/33.22      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 33.02/33.22         = (k5_relat_1 @ sk_C @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['291', '292'])).
% 33.02/33.22  thf('294', plain,
% 33.02/33.22      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 33.02/33.22        (k6_partfun1 @ sk_A))),
% 33.02/33.22      inference('demod', [status(thm)], ['284', '293'])).
% 33.02/33.22  thf('295', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('296', plain,
% 33.02/33.22      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf(dt_k1_partfun1, axiom,
% 33.02/33.22    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 33.02/33.22     ( ( ( v1_funct_1 @ E ) & 
% 33.02/33.22         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 33.02/33.22         ( v1_funct_1 @ F ) & 
% 33.02/33.22         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 33.02/33.22       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 33.02/33.22         ( m1_subset_1 @
% 33.02/33.22           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 33.02/33.22           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 33.02/33.22  thf('297', plain,
% 33.02/33.22      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 33.02/33.22         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 33.02/33.22          | ~ (v1_funct_1 @ X39)
% 33.02/33.22          | ~ (v1_funct_1 @ X42)
% 33.02/33.22          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 33.02/33.22          | (m1_subset_1 @ (k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42) @ 
% 33.02/33.22             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X44))))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 33.02/33.22  thf('298', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.02/33.22         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 33.02/33.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 33.02/33.22          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 33.02/33.22          | ~ (v1_funct_1 @ X1)
% 33.02/33.22          | ~ (v1_funct_1 @ sk_C))),
% 33.02/33.22      inference('sup-', [status(thm)], ['296', '297'])).
% 33.02/33.22  thf('299', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('300', plain,
% 33.02/33.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 33.02/33.22         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 33.02/33.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 33.02/33.22          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 33.02/33.22          | ~ (v1_funct_1 @ X1))),
% 33.02/33.22      inference('demod', [status(thm)], ['298', '299'])).
% 33.02/33.22  thf('301', plain,
% 33.02/33.22      ((~ (v1_funct_1 @ sk_D)
% 33.02/33.22        | (m1_subset_1 @ 
% 33.02/33.22           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 33.02/33.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['295', '300'])).
% 33.02/33.22  thf('302', plain, ((v1_funct_1 @ sk_D)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('303', plain,
% 33.02/33.22      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 33.02/33.22         = (k5_relat_1 @ sk_C @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['291', '292'])).
% 33.02/33.22  thf('304', plain,
% 33.02/33.22      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 33.02/33.22        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 33.02/33.22      inference('demod', [status(thm)], ['301', '302', '303'])).
% 33.02/33.22  thf(redefinition_r2_relset_1, axiom,
% 33.02/33.22    (![A:$i,B:$i,C:$i,D:$i]:
% 33.02/33.22     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 33.02/33.22         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 33.02/33.22       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 33.02/33.22  thf('305', plain,
% 33.02/33.22      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 33.02/33.22         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 33.02/33.22          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 33.02/33.22          | ((X27) = (X30))
% 33.02/33.22          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 33.02/33.22      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 33.02/33.22  thf('306', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 33.02/33.22          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 33.02/33.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['304', '305'])).
% 33.02/33.22  thf('307', plain,
% 33.02/33.22      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 33.02/33.22           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 33.02/33.22        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['294', '306'])).
% 33.02/33.22  thf(dt_k6_partfun1, axiom,
% 33.02/33.22    (![A:$i]:
% 33.02/33.22     ( ( m1_subset_1 @
% 33.02/33.22         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 33.02/33.22       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 33.02/33.22  thf('308', plain,
% 33.02/33.22      (![X46 : $i]:
% 33.02/33.22         (m1_subset_1 @ (k6_partfun1 @ X46) @ 
% 33.02/33.22          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 33.02/33.22  thf('309', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 33.02/33.22      inference('demod', [status(thm)], ['307', '308'])).
% 33.02/33.22  thf('310', plain,
% 33.02/33.22      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 33.02/33.22      inference('demod', [status(thm)], ['24', '25', '26'])).
% 33.02/33.22  thf('311', plain,
% 33.02/33.22      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.22        | ((k4_relat_1 @ sk_D) = (sk_C))
% 33.02/33.22        | ((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B)))),
% 33.02/33.22      inference('demod', [status(thm)], ['283', '309', '310'])).
% 33.02/33.22  thf('312', plain,
% 33.02/33.22      ((((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B))
% 33.02/33.22        | ((k4_relat_1 @ sk_D) = (sk_C))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['311'])).
% 33.02/33.22  thf('313', plain, ((v1_funct_1 @ sk_D)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('314', plain,
% 33.02/33.22      (![X12 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X12)
% 33.02/33.22          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 33.02/33.22          | ~ (v1_funct_1 @ X12)
% 33.02/33.22          | ~ (v1_relat_1 @ X12))),
% 33.02/33.22      inference('cnf', [status(esa)], [d9_funct_1])).
% 33.02/33.22  thf('315', plain,
% 33.02/33.22      ((~ (v1_relat_1 @ sk_D)
% 33.02/33.22        | ((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))
% 33.02/33.22        | ~ (v2_funct_1 @ sk_D))),
% 33.02/33.22      inference('sup-', [status(thm)], ['313', '314'])).
% 33.02/33.22  thf('316', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('317', plain,
% 33.02/33.22      ((((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['315', '316'])).
% 33.02/33.22  thf('318', plain,
% 33.02/33.22      (![X5 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.22      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.22  thf('319', plain,
% 33.02/33.22      (![X6 : $i, X7 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X6)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.22              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.22          | ~ (v1_relat_1 @ X7))),
% 33.02/33.22      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.22  thf('320', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['150', '151'])).
% 33.02/33.22  thf('321', plain,
% 33.02/33.22      (![X6 : $i, X7 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X6)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.22              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.22          | ~ (v1_relat_1 @ X7))),
% 33.02/33.22      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.22  thf('322', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22            = (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['320', '321'])).
% 33.02/33.22  thf('323', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['72', '73', '74'])).
% 33.02/33.22  thf('324', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22            = (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('demod', [status(thm)], ['322', '323'])).
% 33.02/33.22  thf('325', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ X0)))
% 33.02/33.22            = (k5_relat_1 @ sk_C @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 33.02/33.22          | ~ (v1_relat_1 @ sk_C)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['319', '324'])).
% 33.02/33.22  thf('326', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.22      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.22  thf('327', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ X0)))
% 33.02/33.22            = (k5_relat_1 @ sk_C @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('demod', [status(thm)], ['325', '326'])).
% 33.02/33.22  thf('328', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('329', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ X0)))
% 33.02/33.22              = (k5_relat_1 @ sk_C @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 33.02/33.22      inference('clc', [status(thm)], ['327', '328'])).
% 33.02/33.22  thf('330', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ X0)))
% 33.02/33.22            = (k5_relat_1 @ sk_C @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('sup+', [status(thm)], ['318', '329'])).
% 33.02/33.22  thf('331', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ sk_C @ X0)))
% 33.02/33.22              = (k5_relat_1 @ sk_C @ X0)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['330'])).
% 33.02/33.22  thf('332', plain,
% 33.02/33.22      (![X6 : $i, X7 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X6)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.22              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.22          | ~ (v1_relat_1 @ X7))),
% 33.02/33.22      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.22  thf('333', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['45', '46', '47'])).
% 33.02/33.22  thf('334', plain,
% 33.02/33.22      (![X6 : $i, X7 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X6)
% 33.02/33.22          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 33.02/33.22              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 33.02/33.22          | ~ (v1_relat_1 @ X7))),
% 33.02/33.22      inference('cnf', [status(esa)], [t54_relat_1])).
% 33.02/33.22  thf('335', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ X0))
% 33.02/33.22            = (k5_relat_1 @ (k4_relat_1 @ X0) @ sk_D))
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('sup+', [status(thm)], ['333', '334'])).
% 33.02/33.22  thf('336', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['279', '280', '281'])).
% 33.02/33.22  thf('337', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ X0))
% 33.02/33.22            = (k5_relat_1 @ (k4_relat_1 @ X0) @ sk_D))
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('demod', [status(thm)], ['335', '336'])).
% 33.02/33.22  thf('338', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ sk_D)))
% 33.02/33.22            = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ sk_D))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ sk_D)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['332', '337'])).
% 33.02/33.22  thf('339', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('340', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ sk_D)))
% 33.02/33.22            = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ sk_D))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('demod', [status(thm)], ['338', '339'])).
% 33.02/33.22  thf('341', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('342', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ sk_D)))
% 33.02/33.22              = (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ sk_D)))),
% 33.02/33.22      inference('clc', [status(thm)], ['340', '341'])).
% 33.02/33.22  thf(t48_funct_1, axiom,
% 33.02/33.22    (![A:$i]:
% 33.02/33.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 33.02/33.22       ( ![B:$i]:
% 33.02/33.22         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 33.02/33.22           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 33.02/33.22               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 33.02/33.22             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 33.02/33.22  thf('343', plain,
% 33.02/33.22      (![X17 : $i, X18 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X17)
% 33.02/33.22          | ~ (v1_funct_1 @ X17)
% 33.02/33.22          | (v2_funct_1 @ X18)
% 33.02/33.22          | ((k2_relat_1 @ X17) != (k1_relat_1 @ X18))
% 33.02/33.22          | ~ (v2_funct_1 @ (k5_relat_1 @ X17 @ X18))
% 33.02/33.22          | ~ (v1_funct_1 @ X18)
% 33.02/33.22          | ~ (v1_relat_1 @ X18))),
% 33.02/33.22      inference('cnf', [status(esa)], [t48_funct_1])).
% 33.02/33.22  thf('344', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ 
% 33.02/33.22             (k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ sk_D))))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ sk_D)
% 33.02/33.22          | ~ (v1_funct_1 @ sk_D)
% 33.02/33.22          | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 33.02/33.22              != (k1_relat_1 @ sk_D))
% 33.02/33.22          | (v2_funct_1 @ sk_D)
% 33.02/33.22          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['342', '343'])).
% 33.02/33.22  thf('345', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('346', plain, ((v1_funct_1 @ sk_D)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('347', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['2', '9', '12'])).
% 33.02/33.22  thf('348', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ 
% 33.02/33.22             (k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ sk_D))))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))) != (sk_B))
% 33.02/33.22          | (v2_funct_1 @ sk_D)
% 33.02/33.22          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))),
% 33.02/33.22      inference('demod', [status(thm)], ['344', '345', '346', '347'])).
% 33.02/33.22  thf('349', plain,
% 33.02/33.22      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 33.02/33.22        | ~ (v1_relat_1 @ sk_D)
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 33.02/33.22        | (v2_funct_1 @ sk_D)
% 33.02/33.22        | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) != (sk_B))
% 33.02/33.22        | ~ (v1_relat_1 @ sk_C))),
% 33.02/33.22      inference('sup-', [status(thm)], ['331', '348'])).
% 33.02/33.22  thf('350', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('351', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['150', '151'])).
% 33.02/33.22  thf('352', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.22      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.22  thf('353', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['150', '151'])).
% 33.02/33.22  thf('354', plain, ((v1_funct_1 @ sk_C)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('355', plain, (((sk_C) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['150', '151'])).
% 33.02/33.22  thf('356', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 33.02/33.22      inference('sup+', [status(thm)], ['212', '232'])).
% 33.02/33.22  thf('357', plain, ((v1_relat_1 @ sk_C)),
% 33.02/33.22      inference('demod', [status(thm)], ['58', '59'])).
% 33.02/33.22  thf('358', plain,
% 33.02/33.22      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 33.02/33.22        | (v2_funct_1 @ sk_D)
% 33.02/33.22        | ((sk_B) != (sk_B)))),
% 33.02/33.22      inference('demod', [status(thm)],
% 33.02/33.22                ['349', '350', '351', '352', '353', '354', '355', '356', '357'])).
% 33.02/33.22  thf('359', plain,
% 33.02/33.22      (((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['358'])).
% 33.02/33.22  thf('360', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 33.02/33.22      inference('demod', [status(thm)], ['307', '308'])).
% 33.02/33.22  thf('361', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 33.02/33.22      inference('cnf', [status(esa)], [fc4_funct_1])).
% 33.02/33.22  thf('362', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 33.02/33.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.02/33.22  thf('363', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 33.02/33.22      inference('demod', [status(thm)], ['361', '362'])).
% 33.02/33.22  thf('364', plain, ((v2_funct_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['359', '360', '363'])).
% 33.02/33.22  thf('365', plain, (((k2_funct_1 @ sk_D) = (k4_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['317', '364'])).
% 33.02/33.22  thf('366', plain,
% 33.02/33.22      (![X19 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X19)
% 33.02/33.22          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 33.02/33.22          | ~ (v1_funct_1 @ X19)
% 33.02/33.22          | ~ (v1_relat_1 @ X19))),
% 33.02/33.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 33.02/33.22  thf('367', plain,
% 33.02/33.22      ((((k1_relat_1 @ sk_D) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))
% 33.02/33.22        | ~ (v1_relat_1 @ sk_D)
% 33.02/33.22        | ~ (v1_funct_1 @ sk_D)
% 33.02/33.22        | ~ (v2_funct_1 @ sk_D))),
% 33.02/33.22      inference('sup+', [status(thm)], ['365', '366'])).
% 33.02/33.22  thf('368', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['2', '9', '12'])).
% 33.02/33.22  thf('369', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('370', plain, ((v1_funct_1 @ sk_D)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('371', plain, ((v2_funct_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['359', '360', '363'])).
% 33.02/33.22  thf('372', plain, (((sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 33.02/33.22      inference('demod', [status(thm)], ['367', '368', '369', '370', '371'])).
% 33.02/33.22  thf('373', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['45', '46', '47'])).
% 33.02/33.22  thf('374', plain,
% 33.02/33.22      (![X5 : $i]:
% 33.02/33.22         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 33.02/33.22      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 33.02/33.22  thf('375', plain,
% 33.02/33.22      (![X19 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X19)
% 33.02/33.22          | ((k2_relat_1 @ X19) = (k1_relat_1 @ (k2_funct_1 @ X19)))
% 33.02/33.22          | ~ (v1_funct_1 @ X19)
% 33.02/33.22          | ~ (v1_relat_1 @ X19))),
% 33.02/33.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 33.02/33.22  thf('376', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('377', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('378', plain,
% 33.02/33.22      (![X16 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 33.02/33.22          | ~ (v2_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_relat_1 @ X16))),
% 33.02/33.22      inference('cnf', [status(esa)], [fc6_funct_1])).
% 33.02/33.22  thf('379', plain,
% 33.02/33.22      (![X19 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X19)
% 33.02/33.22          | ((k1_relat_1 @ X19) = (k2_relat_1 @ (k2_funct_1 @ X19)))
% 33.02/33.22          | ~ (v1_funct_1 @ X19)
% 33.02/33.22          | ~ (v1_relat_1 @ X19))),
% 33.02/33.22      inference('cnf', [status(esa)], [t55_funct_1])).
% 33.02/33.22  thf(t61_funct_1, axiom,
% 33.02/33.22    (![A:$i]:
% 33.02/33.22     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 33.02/33.22       ( ( v2_funct_1 @ A ) =>
% 33.02/33.22         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 33.02/33.22             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 33.02/33.22           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 33.02/33.22             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 33.02/33.22  thf('380', plain,
% 33.02/33.22      (![X21 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X21)
% 33.02/33.22          | ((k5_relat_1 @ X21 @ (k2_funct_1 @ X21))
% 33.02/33.22              = (k6_relat_1 @ (k1_relat_1 @ X21)))
% 33.02/33.22          | ~ (v1_funct_1 @ X21)
% 33.02/33.22          | ~ (v1_relat_1 @ X21))),
% 33.02/33.22      inference('cnf', [status(esa)], [t61_funct_1])).
% 33.02/33.22  thf('381', plain, (![X53 : $i]: ((k6_partfun1 @ X53) = (k6_relat_1 @ X53))),
% 33.02/33.22      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 33.02/33.22  thf('382', plain,
% 33.02/33.22      (![X21 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X21)
% 33.02/33.22          | ((k5_relat_1 @ X21 @ (k2_funct_1 @ X21))
% 33.02/33.22              = (k6_partfun1 @ (k1_relat_1 @ X21)))
% 33.02/33.22          | ~ (v1_funct_1 @ X21)
% 33.02/33.22          | ~ (v1_relat_1 @ X21))),
% 33.02/33.22      inference('demod', [status(thm)], ['380', '381'])).
% 33.02/33.22  thf('383', plain,
% 33.02/33.22      (![X22 : $i, X23 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X22)
% 33.02/33.22          | ~ (v1_funct_1 @ X22)
% 33.02/33.22          | ((X22) = (k2_funct_1 @ X23))
% 33.02/33.22          | ((k5_relat_1 @ X22 @ X23) != (k6_partfun1 @ (k2_relat_1 @ X23)))
% 33.02/33.22          | ((k2_relat_1 @ X22) != (k1_relat_1 @ X23))
% 33.02/33.22          | ~ (v2_funct_1 @ X23)
% 33.02/33.22          | ~ (v1_funct_1 @ X23)
% 33.02/33.22          | ~ (v1_relat_1 @ X23))),
% 33.02/33.22      inference('demod', [status(thm)], ['177', '178'])).
% 33.02/33.22  thf('384', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 33.02/33.22            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('sup-', [status(thm)], ['382', '383'])).
% 33.02/33.22  thf('385', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 33.02/33.22              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 33.02/33.22      inference('simplify', [status(thm)], ['384'])).
% 33.02/33.22  thf('386', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 33.02/33.22            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['379', '385'])).
% 33.02/33.22  thf('387', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['386'])).
% 33.02/33.22  thf('388', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['378', '387'])).
% 33.02/33.22  thf('389', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['388'])).
% 33.02/33.22  thf('390', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['377', '389'])).
% 33.02/33.22  thf('391', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['390'])).
% 33.02/33.22  thf('392', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['376', '391'])).
% 33.02/33.22  thf('393', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['392'])).
% 33.02/33.22  thf('394', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['375', '393'])).
% 33.02/33.22  thf('395', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['394'])).
% 33.02/33.22  thf('396', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('397', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('398', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('399', plain,
% 33.02/33.22      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 33.02/33.22  thf('400', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['92'])).
% 33.02/33.22  thf('401', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('402', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('403', plain,
% 33.02/33.22      (![X16 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 33.02/33.22          | ~ (v2_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_relat_1 @ X16))),
% 33.02/33.22      inference('cnf', [status(esa)], [fc6_funct_1])).
% 33.02/33.22  thf('404', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('405', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('406', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['92'])).
% 33.02/33.22  thf('407', plain,
% 33.02/33.22      (![X16 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k2_funct_1 @ X16))
% 33.02/33.22          | ~ (v2_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_funct_1 @ X16)
% 33.02/33.22          | ~ (v1_relat_1 @ X16))),
% 33.02/33.22      inference('cnf', [status(esa)], [fc6_funct_1])).
% 33.02/33.22  thf('408', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['406', '407'])).
% 33.02/33.22  thf('409', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['405', '408'])).
% 33.02/33.22  thf('410', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['409'])).
% 33.02/33.22  thf('411', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['404', '410'])).
% 33.02/33.22  thf('412', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['411'])).
% 33.02/33.22  thf('413', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['403', '412'])).
% 33.02/33.22  thf('414', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['413'])).
% 33.02/33.22  thf('415', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['92'])).
% 33.02/33.22  thf('416', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k2_funct_1 @ (k2_funct_1 @ X0)) = (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['90'])).
% 33.02/33.22  thf('417', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['415', '416'])).
% 33.02/33.22  thf('418', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('sup-', [status(thm)], ['414', '417'])).
% 33.02/33.22  thf('419', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['418'])).
% 33.02/33.22  thf('420', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['402', '419'])).
% 33.02/33.22  thf('421', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['420'])).
% 33.02/33.22  thf('422', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22              = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['401', '421'])).
% 33.02/33.22  thf('423', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22            = (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['422'])).
% 33.02/33.22  thf('424', plain,
% 33.02/33.22      (![X13 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 33.02/33.22          | ~ (v1_funct_1 @ X13)
% 33.02/33.22          | ~ (v1_relat_1 @ X13))),
% 33.02/33.22      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 33.02/33.22  thf('425', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('sup+', [status(thm)], ['423', '424'])).
% 33.02/33.22  thf('426', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['400', '425'])).
% 33.02/33.22  thf('427', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ (k2_funct_1 @ X0))))),
% 33.02/33.22      inference('simplify', [status(thm)], ['426'])).
% 33.02/33.22  thf('428', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 33.02/33.22      inference('sup-', [status(thm)], ['399', '427'])).
% 33.02/33.22  thf('429', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['398', '428'])).
% 33.02/33.22  thf('430', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['429'])).
% 33.02/33.22  thf('431', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('sup-', [status(thm)], ['397', '430'])).
% 33.02/33.22  thf('432', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X0)
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['431'])).
% 33.02/33.22  thf('433', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v2_funct_1 @ X0))),
% 33.02/33.22      inference('sup-', [status(thm)], ['396', '432'])).
% 33.02/33.22  thf('434', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X0)
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0))),
% 33.02/33.22      inference('simplify', [status(thm)], ['433'])).
% 33.02/33.22  thf('435', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v2_funct_1 @ X0))),
% 33.02/33.22      inference('sup+', [status(thm)], ['395', '434'])).
% 33.02/33.22  thf('436', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         (~ (v2_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('simplify', [status(thm)], ['435'])).
% 33.02/33.22  thf('437', plain,
% 33.02/33.22      (![X0 : $i]:
% 33.02/33.22         ((v1_funct_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ X0)
% 33.02/33.22          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 33.02/33.22          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 33.02/33.22          | ~ (v2_funct_1 @ (k4_relat_1 @ X0)))),
% 33.02/33.22      inference('sup+', [status(thm)], ['374', '436'])).
% 33.02/33.22  thf('438', plain,
% 33.02/33.22      ((~ (v1_relat_1 @ sk_D)
% 33.02/33.22        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 33.02/33.22        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 33.02/33.22        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 33.02/33.22        | (v1_funct_1 @ (k4_relat_1 @ sk_D)))),
% 33.02/33.22      inference('sup-', [status(thm)], ['373', '437'])).
% 33.02/33.22  thf('439', plain, ((v1_relat_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['20', '21'])).
% 33.02/33.22  thf('440', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['45', '46', '47'])).
% 33.02/33.22  thf('441', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['45', '46', '47'])).
% 33.02/33.22  thf('442', plain, ((v1_funct_1 @ sk_D)),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('443', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['279', '280', '281'])).
% 33.02/33.22  thf('444', plain,
% 33.02/33.22      ((~ (v2_funct_1 @ sk_D) | (v1_funct_1 @ (k4_relat_1 @ sk_D)))),
% 33.02/33.22      inference('demod', [status(thm)],
% 33.02/33.22                ['438', '439', '440', '441', '442', '443'])).
% 33.02/33.22  thf('445', plain, ((v2_funct_1 @ sk_D)),
% 33.02/33.22      inference('demod', [status(thm)], ['359', '360', '363'])).
% 33.02/33.22  thf('446', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['444', '445'])).
% 33.02/33.22  thf('447', plain, ((((sk_B) != (sk_B)) | ((k4_relat_1 @ sk_D) = (sk_C)))),
% 33.02/33.22      inference('demod', [status(thm)], ['312', '372', '446'])).
% 33.02/33.22  thf('448', plain, (((k4_relat_1 @ sk_D) = (sk_C))),
% 33.02/33.22      inference('simplify', [status(thm)], ['447'])).
% 33.02/33.22  thf('449', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 33.02/33.22      inference('demod', [status(thm)], ['48', '448'])).
% 33.02/33.22  thf('450', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 33.02/33.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 33.02/33.22  thf('451', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['55', '60', '61'])).
% 33.02/33.22  thf('452', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 33.02/33.22      inference('demod', [status(thm)], ['450', '451'])).
% 33.02/33.22  thf('453', plain, ($false),
% 33.02/33.22      inference('simplify_reflect-', [status(thm)], ['449', '452'])).
% 33.02/33.22  
% 33.02/33.22  % SZS output end Refutation
% 33.02/33.22  
% 33.02/33.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

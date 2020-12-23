%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1puoXhh4SR

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:19 EST 2020

% Result     : Theorem 37.73s
% Output     : Refutation 37.73s
% Verified   : 
% Statistics : Number of formulae       :  471 (13164 expanded)
%              Number of leaves         :   56 (4205 expanded)
%              Depth                    :   33
%              Number of atoms          : 4145 (196978 expanded)
%              Number of equality atoms :  320 (15627 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
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
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
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
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
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

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('34',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('41',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k6_partfun1 @ X1 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','42'])).

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
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('64',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','61','64'])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('67',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['67','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('75',plain,
    ( ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['67','72'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('78',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('80',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('84',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X55 @ X54 @ X53 )
       != X54 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X53 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('87',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['87','88','89','90','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('95',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('97',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['84','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','104'])).

thf('106',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['50','107'])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['49','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('111',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','110'])).

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

thf('112',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X21
        = ( k2_funct_1 @ X22 ) )
      | ( ( k5_relat_1 @ X21 @ X22 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X22 ) ) )
      | ( ( k2_relat_1 @ X21 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('113',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('114',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X21
        = ( k2_funct_1 @ X22 ) )
      | ( ( k5_relat_1 @ X21 @ X22 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X22 ) ) )
      | ( ( k2_relat_1 @ X21 )
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
     != ( k6_partfun1 @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k4_relat_1 @ sk_D )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('117',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('118',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('119',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('120',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('121',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['119','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['117','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('132',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','61','64'])).

thf('133',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['127','128','129','130','131','132'])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['116','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('136',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('138',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X55 @ X54 @ X53 )
       != X54 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X53 @ X55 @ X54 )
      | ~ ( v1_funct_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['141','142','143','144','145'])).

thf('147',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['138','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('154',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('155',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X56 ) ) )
      | ( ( k5_relat_1 @ X57 @ ( k2_funct_1 @ X57 ) )
        = ( k6_partfun1 @ X58 ) )
      | ~ ( v2_funct_1 @ X57 )
      | ( ( k2_relset_1 @ X58 @ X56 @ X57 )
       != X56 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('156',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['156','157','158','159','160'])).

thf('162',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['153','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['165','166','167','168'])).

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

thf('170',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('171',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('173',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('174',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('176',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('177',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('178',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('179',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('180',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('181',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('182',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['180','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['179','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['178','187'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['188','189','190','191','192'])).

thf('194',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['177','193'])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('196',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('199',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['171','174','175','176','196','197','198'])).

thf('200',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('202',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('204',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('205',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['202','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('208',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('210',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('211',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('212',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['210','213'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['209','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ( ( k4_relat_1 @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['208','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('223',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X20 ) @ X20 ) )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('224',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( X56 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X58 @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X56 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X57 ) @ X57 )
        = ( k6_partfun1 @ X56 ) )
      | ~ ( v2_funct_1 @ X57 )
      | ( ( k2_relset_1 @ X58 @ X56 @ X57 )
       != X56 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('231',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('235',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('236',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['231','232','233','234','235','236'])).

thf('238',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['238','239'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('241',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('242',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('243',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['228','240','243'])).

thf('245',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','244'])).

thf('246',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('247',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['216'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['246','250'])).

thf('252',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('253',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('254',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('255',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['256','257'])).

thf('259',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['253','258'])).

thf('260',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['54','61','64'])).

thf('261',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('262',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
      = sk_C )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['259','260','261'])).

thf('263',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['252','262'])).

thf('264',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('265',plain,
    ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    = sk_C ),
    inference(demod,[status(thm)],['263','264'])).

thf('266',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('267',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('268',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['199'])).

thf('269',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['251','265','266','267','268'])).

thf('270',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
     != ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['115','136','137','152','200','245','269'])).

thf('271',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('272',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('273',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('274',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['275'])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('281',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['278'])).

thf('282',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('283',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['281','282'])).

thf('284',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['280','284'])).

thf('286',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) )
        = X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['279','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['278'])).

thf('290',plain,(
    ! [X11: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('291',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('292',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('293',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['291','292'])).

thf('294',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['290','293'])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['294'])).

thf('296',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('298',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['289','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['288','299'])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['272','300'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['295','296'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['301','302'])).

thf('304',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['271','303'])).

thf('305',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('306',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('307',plain,
    ( ( ( k4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
     != ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['270','306'])).

thf('308',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
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

thf('310',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('311',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['308','313'])).

thf('315',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
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

thf('319',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('320',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['318','319'])).

thf('321',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['320','321'])).

thf('323',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['317','322'])).

thf('324',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['323','324'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('326',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('327',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['325','326'])).

thf('328',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['316','327'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('329',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('330',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['314','315','330'])).

thf('332',plain,(
    ! [X10: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X10 ) )
      = ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('333',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['307','331','332'])).

thf('334',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) )
     != sk_B ) ),
    inference(simplify,[status(thm)],['333'])).

thf('335',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('336',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('337',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('338',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('339',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('340',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('341',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['339','340'])).

thf('342',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['341'])).

thf('343',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['338','342'])).

thf('344',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['337','343'])).

thf('345',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['344'])).

thf('346',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['336','345'])).

thf('347',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('348',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('349',plain,
    ( ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['346','347','348'])).

thf('350',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['335','349'])).

thf('351',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('352',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['350','351'])).

thf('353',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('354',plain,(
    ! [X5: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X5 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('355',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('356',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['354','355'])).

thf('357',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['353','356'])).

thf('358',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('359',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ sk_C ) ) )
        = ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['357','358'])).

thf('360',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('361',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X6 ) @ ( k4_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('362',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v2_funct_1 @ X17 )
      | ( ( k2_relat_1 @ X16 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X16 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('363',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X1 ) )
      | ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
       != ( k1_relat_1 @ ( k4_relat_1 @ X1 ) ) )
      | ( v2_funct_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['361','362'])).

thf('364',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['360','363'])).

thf('365',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('366',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('367',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('368',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('370',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('371',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('372',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k4_relat_1 @ X0 ) )
       != sk_B )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['364','365','366','367','368','369','370','371'])).

thf('373',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['359','372'])).

thf('374',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('375',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('376',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('377',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('378',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('380',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('381',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('382',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['228','240','243'])).

thf('383',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_D )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['373','374','375','376','377','378','379','380','381','382'])).

thf('384',plain,
    ( ( v2_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['383'])).

thf('385',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['314','315','330'])).

thf('386',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('387',plain,(
    v2_funct_1 @ sk_D ),
    inference(demod,[status(thm)],['384','385','386'])).

thf('388',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['352','387'])).

thf('389',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('390',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('391',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k4_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('392',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['390','391'])).

thf('393',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('394',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('395',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('396',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('397',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['392','393','394','395','396'])).

thf('398',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_B
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['389','397'])).

thf('399',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['20','21'])).

thf('400',plain,
    ( ( sk_B
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['398','399'])).

thf('401',plain,(
    v2_funct_1 @ sk_D ),
    inference(demod,[status(thm)],['384','385','386'])).

thf('402',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['400','401'])).

thf('403',plain,
    ( ( ( k4_relat_1 @ sk_D )
      = sk_C )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['334','388','402'])).

thf('404',plain,
    ( ( k4_relat_1 @ sk_D )
    = sk_C ),
    inference(simplify,[status(thm)],['403'])).

thf('405',plain,
    ( ( k4_relat_1 @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['48','404'])).

thf('406',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ X12 )
        = ( k4_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('407',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('408',plain,
    ( ( sk_D
     != ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['406','407'])).

thf('409',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('410',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('411',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('412',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['408','409','410','411'])).

thf('413',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['405','412'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1puoXhh4SR
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:10:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 37.73/37.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 37.73/37.93  % Solved by: fo/fo7.sh
% 37.73/37.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 37.73/37.93  % done 8818 iterations in 37.457s
% 37.73/37.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 37.73/37.93  % SZS output start Refutation
% 37.73/37.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 37.73/37.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 37.73/37.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 37.73/37.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 37.73/37.93  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 37.73/37.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 37.73/37.93  thf(sk_D_type, type, sk_D: $i).
% 37.73/37.93  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 37.73/37.93  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 37.73/37.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 37.73/37.93  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 37.73/37.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 37.73/37.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 37.73/37.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 37.73/37.93  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 37.73/37.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 37.73/37.93  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 37.73/37.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 37.73/37.93  thf(sk_B_type, type, sk_B: $i).
% 37.73/37.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 37.73/37.93  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 37.73/37.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 37.73/37.93  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 37.73/37.93  thf(sk_C_type, type, sk_C: $i).
% 37.73/37.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 37.73/37.93  thf(sk_A_type, type, sk_A: $i).
% 37.73/37.93  thf(t36_funct_2, conjecture,
% 37.73/37.93    (![A:$i,B:$i,C:$i]:
% 37.73/37.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.73/37.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.73/37.93       ( ![D:$i]:
% 37.73/37.93         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 37.73/37.93             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 37.73/37.93           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 37.73/37.93               ( r2_relset_1 @
% 37.73/37.93                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 37.73/37.93                 ( k6_partfun1 @ A ) ) & 
% 37.73/37.93               ( v2_funct_1 @ C ) ) =>
% 37.73/37.93             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 37.73/37.93               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 37.73/37.93  thf(zf_stmt_0, negated_conjecture,
% 37.73/37.93    (~( ![A:$i,B:$i,C:$i]:
% 37.73/37.93        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.73/37.93            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.73/37.93          ( ![D:$i]:
% 37.73/37.93            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 37.73/37.93                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 37.73/37.93              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 37.73/37.93                  ( r2_relset_1 @
% 37.73/37.93                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 37.73/37.93                    ( k6_partfun1 @ A ) ) & 
% 37.73/37.93                  ( v2_funct_1 @ C ) ) =>
% 37.73/37.93                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 37.73/37.93                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 37.73/37.93    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 37.73/37.93  thf('0', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(d1_funct_2, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i]:
% 37.73/37.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 37.73/37.93       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 37.73/37.93           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 37.73/37.93             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 37.73/37.93         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 37.73/37.93           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 37.73/37.93             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 37.73/37.93  thf(zf_stmt_1, axiom,
% 37.73/37.93    (![C:$i,B:$i,A:$i]:
% 37.73/37.93     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 37.73/37.93       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 37.73/37.93  thf('1', plain,
% 37.73/37.93      (![X32 : $i, X33 : $i, X34 : $i]:
% 37.73/37.93         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 37.73/37.93          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 37.73/37.93          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 37.73/37.93  thf('2', plain,
% 37.73/37.93      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 37.73/37.93        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['0', '1'])).
% 37.73/37.93  thf(zf_stmt_2, axiom,
% 37.73/37.93    (![B:$i,A:$i]:
% 37.73/37.93     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 37.73/37.93       ( zip_tseitin_0 @ B @ A ) ))).
% 37.73/37.93  thf('3', plain,
% 37.73/37.93      (![X30 : $i, X31 : $i]:
% 37.73/37.93         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 37.73/37.93  thf('4', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 37.73/37.93  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 37.73/37.93  thf(zf_stmt_5, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i]:
% 37.73/37.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 37.73/37.93       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 37.73/37.93         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 37.73/37.93           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 37.73/37.93             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 37.73/37.93  thf('5', plain,
% 37.73/37.93      (![X35 : $i, X36 : $i, X37 : $i]:
% 37.73/37.93         (~ (zip_tseitin_0 @ X35 @ X36)
% 37.73/37.93          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 37.73/37.93          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 37.73/37.93  thf('6', plain,
% 37.73/37.93      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 37.73/37.93      inference('sup-', [status(thm)], ['4', '5'])).
% 37.73/37.93  thf('7', plain,
% 37.73/37.93      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 37.73/37.93      inference('sup-', [status(thm)], ['3', '6'])).
% 37.73/37.93  thf('8', plain, (((sk_A) != (k1_xboole_0))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('9', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 37.73/37.93      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 37.73/37.93  thf('10', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(redefinition_k1_relset_1, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i]:
% 37.73/37.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 37.73/37.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 37.73/37.93  thf('11', plain,
% 37.73/37.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 37.73/37.93         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 37.73/37.93          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 37.73/37.93  thf('12', plain,
% 37.73/37.93      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 37.73/37.93      inference('sup-', [status(thm)], ['10', '11'])).
% 37.73/37.93  thf('13', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['2', '9', '12'])).
% 37.73/37.93  thf(t78_relat_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( v1_relat_1 @ A ) =>
% 37.73/37.93       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 37.73/37.93  thf('14', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('cnf', [status(esa)], [t78_relat_1])).
% 37.73/37.93  thf(redefinition_k6_partfun1, axiom,
% 37.73/37.93    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 37.73/37.93  thf('15', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.73/37.93  thf('16', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('17', plain,
% 37.73/37.93      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_D))),
% 37.73/37.93      inference('sup+', [status(thm)], ['13', '16'])).
% 37.73/37.93  thf('18', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(cc2_relat_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( v1_relat_1 @ A ) =>
% 37.73/37.93       ( ![B:$i]:
% 37.73/37.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 37.73/37.93  thf('19', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 37.73/37.93          | (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 37.73/37.93  thf('20', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 37.73/37.93      inference('sup-', [status(thm)], ['18', '19'])).
% 37.73/37.93  thf(fc6_relat_1, axiom,
% 37.73/37.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 37.73/37.93  thf('21', plain,
% 37.73/37.93      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 37.73/37.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 37.73/37.93  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['20', '21'])).
% 37.73/37.93  thf('23', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['17', '22'])).
% 37.73/37.93  thf(t72_relat_1, axiom,
% 37.73/37.93    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 37.73/37.93  thf('24', plain,
% 37.73/37.93      (![X10 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X10)) = (k6_relat_1 @ X10))),
% 37.73/37.93      inference('cnf', [status(esa)], [t72_relat_1])).
% 37.73/37.93  thf('25', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.73/37.93  thf('26', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.73/37.93  thf('27', plain,
% 37.73/37.93      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 37.73/37.93      inference('demod', [status(thm)], ['24', '25', '26'])).
% 37.73/37.93  thf(t54_relat_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( v1_relat_1 @ A ) =>
% 37.73/37.93       ( ![B:$i]:
% 37.73/37.93         ( ( v1_relat_1 @ B ) =>
% 37.73/37.93           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 37.73/37.93             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 37.73/37.93  thf('28', plain,
% 37.73/37.93      (![X6 : $i, X7 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X6)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 37.73/37.93              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 37.73/37.93          | ~ (v1_relat_1 @ X7))),
% 37.73/37.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 37.73/37.93  thf('29', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 37.73/37.93            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 37.73/37.93          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('sup+', [status(thm)], ['27', '28'])).
% 37.73/37.93  thf(fc4_funct_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 37.73/37.93       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 37.73/37.93  thf('30', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 37.73/37.93      inference('cnf', [status(esa)], [fc4_funct_1])).
% 37.73/37.93  thf('31', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.73/37.93  thf('32', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 37.73/37.93      inference('demod', [status(thm)], ['30', '31'])).
% 37.73/37.93  thf('33', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 37.73/37.93            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('demod', [status(thm)], ['29', '32'])).
% 37.73/37.93  thf(involutiveness_k4_relat_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 37.73/37.93  thf('34', plain,
% 37.73/37.93      (![X5 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 37.73/37.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 37.73/37.93  thf('35', plain,
% 37.73/37.93      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 37.73/37.93      inference('demod', [status(thm)], ['24', '25', '26'])).
% 37.73/37.93  thf('36', plain,
% 37.73/37.93      (![X6 : $i, X7 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X6)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 37.73/37.93              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 37.73/37.93          | ~ (v1_relat_1 @ X7))),
% 37.73/37.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 37.73/37.93  thf('37', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 37.73/37.93          | ~ (v1_relat_1 @ X1)
% 37.73/37.93          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['35', '36'])).
% 37.73/37.93  thf('38', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 37.73/37.93      inference('demod', [status(thm)], ['30', '31'])).
% 37.73/37.93  thf('39', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('demod', [status(thm)], ['37', '38'])).
% 37.73/37.93  thf('40', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_partfun1 @ X1)))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['34', '39'])).
% 37.73/37.93  thf(dt_k4_relat_1, axiom,
% 37.73/37.93    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 37.73/37.93  thf('41', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('42', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k5_relat_1 @ (k4_relat_1 @ X0) @ (k6_partfun1 @ X1)))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 37.73/37.93      inference('clc', [status(thm)], ['40', '41'])).
% 37.73/37.93  thf('43', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['33', '42'])).
% 37.73/37.93  thf('44', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['43'])).
% 37.73/37.93  thf('45', plain,
% 37.73/37.93      ((((k4_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_D))),
% 37.73/37.93      inference('sup+', [status(thm)], ['23', '44'])).
% 37.73/37.93  thf('46', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['17', '22'])).
% 37.73/37.93  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['20', '21'])).
% 37.73/37.93  thf('48', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('49', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('50', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('51', plain,
% 37.73/37.93      (![X5 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 37.73/37.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 37.73/37.93  thf('52', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('53', plain,
% 37.73/37.93      (![X32 : $i, X33 : $i, X34 : $i]:
% 37.73/37.93         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 37.73/37.93          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 37.73/37.93          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 37.73/37.93  thf('54', plain,
% 37.73/37.93      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 37.73/37.93        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['52', '53'])).
% 37.73/37.93  thf('55', plain,
% 37.73/37.93      (![X30 : $i, X31 : $i]:
% 37.73/37.93         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 37.73/37.93  thf('56', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('57', plain,
% 37.73/37.93      (![X35 : $i, X36 : $i, X37 : $i]:
% 37.73/37.93         (~ (zip_tseitin_0 @ X35 @ X36)
% 37.73/37.93          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 37.73/37.93          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_5])).
% 37.73/37.93  thf('58', plain,
% 37.73/37.93      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 37.73/37.93      inference('sup-', [status(thm)], ['56', '57'])).
% 37.73/37.93  thf('59', plain,
% 37.73/37.93      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 37.73/37.93      inference('sup-', [status(thm)], ['55', '58'])).
% 37.73/37.93  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('61', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 37.73/37.93      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 37.73/37.93  thf('62', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('63', plain,
% 37.73/37.93      (![X23 : $i, X24 : $i, X25 : $i]:
% 37.73/37.93         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 37.73/37.93          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 37.73/37.93  thf('64', plain,
% 37.73/37.93      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['62', '63'])).
% 37.73/37.93  thf('65', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['54', '61', '64'])).
% 37.73/37.93  thf('66', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('67', plain,
% 37.73/37.93      ((((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C))),
% 37.73/37.93      inference('sup+', [status(thm)], ['65', '66'])).
% 37.73/37.93  thf('68', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('69', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 37.73/37.93          | (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 37.73/37.93  thf('70', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['68', '69'])).
% 37.73/37.93  thf('71', plain,
% 37.73/37.93      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 37.73/37.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 37.73/37.93  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('73', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['67', '72'])).
% 37.73/37.93  thf('74', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['43'])).
% 37.73/37.93  thf('75', plain,
% 37.73/37.93      ((((k4_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C))),
% 37.73/37.93      inference('sup+', [status(thm)], ['73', '74'])).
% 37.73/37.93  thf('76', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['67', '72'])).
% 37.73/37.93  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('78', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('79', plain,
% 37.73/37.93      (![X5 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 37.73/37.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 37.73/37.93  thf('80', plain,
% 37.73/37.93      (![X6 : $i, X7 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X6)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 37.73/37.93              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 37.73/37.93          | ~ (v1_relat_1 @ X7))),
% 37.73/37.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 37.73/37.93  thf('81', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 37.73/37.93            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('sup+', [status(thm)], ['79', '80'])).
% 37.73/37.93  thf('82', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ sk_C)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k5_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ X0))
% 37.73/37.93              = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['78', '81'])).
% 37.73/37.93  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf(d9_funct_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.73/37.93       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 37.73/37.93  thf('84', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf('85', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(t31_funct_2, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i]:
% 37.73/37.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.73/37.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.73/37.93       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 37.73/37.93         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 37.73/37.93           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 37.73/37.93           ( m1_subset_1 @
% 37.73/37.93             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 37.73/37.93  thf('86', plain,
% 37.73/37.93      (![X53 : $i, X54 : $i, X55 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X53)
% 37.73/37.93          | ((k2_relset_1 @ X55 @ X54 @ X53) != (X54))
% 37.73/37.93          | (m1_subset_1 @ (k2_funct_1 @ X53) @ 
% 37.73/37.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 37.73/37.93          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 37.73/37.93          | ~ (v1_funct_2 @ X53 @ X55 @ X54)
% 37.73/37.93          | ~ (v1_funct_1 @ X53))),
% 37.73/37.93      inference('cnf', [status(esa)], [t31_funct_2])).
% 37.73/37.93  thf('87', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.73/37.93        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 37.73/37.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 37.73/37.93        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['85', '86'])).
% 37.73/37.93  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('89', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('90', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('91', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('92', plain,
% 37.73/37.93      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 37.73/37.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 37.73/37.93        | ((sk_B) != (sk_B)))),
% 37.73/37.93      inference('demod', [status(thm)], ['87', '88', '89', '90', '91'])).
% 37.73/37.93  thf('93', plain,
% 37.73/37.93      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 37.73/37.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['92'])).
% 37.73/37.93  thf('94', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 37.73/37.93          | (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 37.73/37.93  thf('95', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 37.73/37.93        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['93', '94'])).
% 37.73/37.93  thf('96', plain,
% 37.73/37.93      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 37.73/37.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 37.73/37.93  thf('97', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['95', '96'])).
% 37.73/37.93  thf('98', plain,
% 37.73/37.93      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup+', [status(thm)], ['84', '97'])).
% 37.73/37.93  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('102', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 37.73/37.93  thf('103', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('104', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ X0))
% 37.73/37.93              = (k5_relat_1 @ (k4_relat_1 @ X0) @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('demod', [status(thm)], ['82', '83', '102', '103'])).
% 37.73/37.93  thf('105', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 37.73/37.93            = (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['51', '104'])).
% 37.73/37.93  thf('106', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('107', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0)))
% 37.73/37.93              = (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('clc', [status(thm)], ['105', '106'])).
% 37.73/37.93  thf('108', plain,
% 37.73/37.93      ((((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 37.73/37.93          = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['50', '107'])).
% 37.73/37.93  thf('109', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ sk_D)
% 37.73/37.93        | ((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 37.73/37.93            = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['49', '108'])).
% 37.73/37.93  thf('110', plain, ((v1_relat_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['20', '21'])).
% 37.73/37.93  thf('111', plain,
% 37.73/37.93      (((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 37.73/37.93         = (k5_relat_1 @ (k4_relat_1 @ sk_D) @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['109', '110'])).
% 37.73/37.93  thf(t64_funct_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.73/37.93       ( ![B:$i]:
% 37.73/37.93         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 37.73/37.93           ( ( ( v2_funct_1 @ A ) & 
% 37.73/37.93               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 37.73/37.93               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 37.73/37.93             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 37.73/37.93  thf('112', plain,
% 37.73/37.93      (![X21 : $i, X22 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X21)
% 37.73/37.93          | ~ (v1_funct_1 @ X21)
% 37.73/37.93          | ((X21) = (k2_funct_1 @ X22))
% 37.73/37.93          | ((k5_relat_1 @ X21 @ X22) != (k6_relat_1 @ (k2_relat_1 @ X22)))
% 37.73/37.93          | ((k2_relat_1 @ X21) != (k1_relat_1 @ X22))
% 37.73/37.93          | ~ (v2_funct_1 @ X22)
% 37.73/37.93          | ~ (v1_funct_1 @ X22)
% 37.73/37.93          | ~ (v1_relat_1 @ X22))),
% 37.73/37.93      inference('cnf', [status(esa)], [t64_funct_1])).
% 37.73/37.93  thf('113', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.73/37.93  thf('114', plain,
% 37.73/37.93      (![X21 : $i, X22 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X21)
% 37.73/37.93          | ~ (v1_funct_1 @ X21)
% 37.73/37.93          | ((X21) = (k2_funct_1 @ X22))
% 37.73/37.93          | ((k5_relat_1 @ X21 @ X22) != (k6_partfun1 @ (k2_relat_1 @ X22)))
% 37.73/37.93          | ((k2_relat_1 @ X21) != (k1_relat_1 @ X22))
% 37.73/37.93          | ~ (v2_funct_1 @ X22)
% 37.73/37.93          | ~ (v1_funct_1 @ X22)
% 37.73/37.93          | ~ (v1_relat_1 @ X22))),
% 37.73/37.93      inference('demod', [status(thm)], ['112', '113'])).
% 37.73/37.93  thf('115', plain,
% 37.73/37.93      ((((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 37.73/37.93          != (k6_partfun1 @ (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ((k2_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93            != (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ((k4_relat_1 @ sk_D) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['111', '114'])).
% 37.73/37.93  thf('116', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('117', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('118', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('119', plain,
% 37.73/37.93      (![X5 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 37.73/37.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 37.73/37.93  thf('120', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf(t55_funct_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.73/37.93       ( ( v2_funct_1 @ A ) =>
% 37.73/37.93         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 37.73/37.93           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 37.73/37.93  thf('121', plain,
% 37.73/37.93      (![X18 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X18)
% 37.73/37.93          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 37.73/37.93          | ~ (v1_funct_1 @ X18)
% 37.73/37.93          | ~ (v1_relat_1 @ X18))),
% 37.73/37.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 37.73/37.93  thf('122', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0)))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['120', '121'])).
% 37.73/37.93  thf('123', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k1_relat_1 @ X0) = (k2_relat_1 @ (k4_relat_1 @ X0))))),
% 37.73/37.93      inference('simplify', [status(thm)], ['122'])).
% 37.73/37.93  thf('124', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k1_relat_1 @ (k4_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['119', '123'])).
% 37.73/37.93  thf('125', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k1_relat_1 @ (k4_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['118', '124'])).
% 37.73/37.93  thf('126', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k1_relat_1 @ (k4_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('simplify', [status(thm)], ['125'])).
% 37.73/37.93  thf('127', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93            = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['117', '126'])).
% 37.73/37.93  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('129', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('131', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('132', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['54', '61', '64'])).
% 37.73/37.93  thf('133', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('demod', [status(thm)],
% 37.73/37.93                ['127', '128', '129', '130', '131', '132'])).
% 37.73/37.93  thf('134', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ sk_C) | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['116', '133'])).
% 37.73/37.93  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('136', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['134', '135'])).
% 37.73/37.93  thf('137', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 37.73/37.93  thf('138', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf('139', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('140', plain,
% 37.73/37.93      (![X53 : $i, X54 : $i, X55 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X53)
% 37.73/37.93          | ((k2_relset_1 @ X55 @ X54 @ X53) != (X54))
% 37.73/37.93          | (v1_funct_1 @ (k2_funct_1 @ X53))
% 37.73/37.93          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 37.73/37.93          | ~ (v1_funct_2 @ X53 @ X55 @ X54)
% 37.73/37.93          | ~ (v1_funct_1 @ X53))),
% 37.73/37.93      inference('cnf', [status(esa)], [t31_funct_2])).
% 37.73/37.93  thf('141', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.73/37.93        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 37.73/37.93        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['139', '140'])).
% 37.73/37.93  thf('142', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('143', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('144', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('145', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('146', plain,
% 37.73/37.93      (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 37.73/37.93      inference('demod', [status(thm)], ['141', '142', '143', '144', '145'])).
% 37.73/37.93  thf('147', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 37.73/37.93      inference('simplify', [status(thm)], ['146'])).
% 37.73/37.93  thf('148', plain,
% 37.73/37.93      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup+', [status(thm)], ['138', '147'])).
% 37.73/37.93  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('152', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 37.73/37.93  thf('153', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf('154', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(t35_funct_2, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i]:
% 37.73/37.93     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 37.73/37.93         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.73/37.93       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 37.73/37.93         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 37.73/37.93           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 37.73/37.93             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 37.73/37.93  thf('155', plain,
% 37.73/37.93      (![X56 : $i, X57 : $i, X58 : $i]:
% 37.73/37.93         (((X56) = (k1_xboole_0))
% 37.73/37.93          | ~ (v1_funct_1 @ X57)
% 37.73/37.93          | ~ (v1_funct_2 @ X57 @ X58 @ X56)
% 37.73/37.93          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 37.73/37.93          | ((k5_relat_1 @ X57 @ (k2_funct_1 @ X57)) = (k6_partfun1 @ X58))
% 37.73/37.93          | ~ (v2_funct_1 @ X57)
% 37.73/37.93          | ((k2_relset_1 @ X58 @ X56 @ X57) != (X56)))),
% 37.73/37.93      inference('cnf', [status(esa)], [t35_funct_2])).
% 37.73/37.93  thf('156', plain,
% 37.73/37.93      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C)
% 37.73/37.93        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 37.73/37.93        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ((sk_B) = (k1_xboole_0)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['154', '155'])).
% 37.73/37.93  thf('157', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('158', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('159', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('161', plain,
% 37.73/37.93      ((((sk_B) != (sk_B))
% 37.73/37.93        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 37.73/37.93        | ((sk_B) = (k1_xboole_0)))),
% 37.73/37.93      inference('demod', [status(thm)], ['156', '157', '158', '159', '160'])).
% 37.73/37.93  thf('162', plain,
% 37.73/37.93      ((((sk_B) = (k1_xboole_0))
% 37.73/37.93        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['161'])).
% 37.73/37.93  thf('163', plain, (((sk_B) != (k1_xboole_0))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('164', plain,
% 37.73/37.93      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 37.73/37.93      inference('simplify_reflect-', [status(thm)], ['162', '163'])).
% 37.73/37.93  thf('165', plain,
% 37.73/37.93      ((((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup+', [status(thm)], ['153', '164'])).
% 37.73/37.93  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('169', plain,
% 37.73/37.93      (((k5_relat_1 @ sk_C @ (k4_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 37.73/37.93      inference('demod', [status(thm)], ['165', '166', '167', '168'])).
% 37.73/37.93  thf(t48_funct_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.73/37.93       ( ![B:$i]:
% 37.73/37.93         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 37.73/37.93           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 37.73/37.93               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 37.73/37.93             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 37.73/37.93  thf('170', plain,
% 37.73/37.93      (![X16 : $i, X17 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X16)
% 37.73/37.93          | ~ (v1_funct_1 @ X16)
% 37.73/37.93          | (v2_funct_1 @ X17)
% 37.73/37.93          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 37.73/37.93          | ~ (v2_funct_1 @ (k5_relat_1 @ X16 @ X17))
% 37.73/37.93          | ~ (v1_funct_1 @ X17)
% 37.73/37.93          | ~ (v1_relat_1 @ X17))),
% 37.73/37.93      inference('cnf', [status(esa)], [t48_funct_1])).
% 37.73/37.93  thf('171', plain,
% 37.73/37.93      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['169', '170'])).
% 37.73/37.93  thf('172', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 37.73/37.93      inference('cnf', [status(esa)], [fc4_funct_1])).
% 37.73/37.93  thf('173', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.73/37.93  thf('174', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 37.73/37.93      inference('demod', [status(thm)], ['172', '173'])).
% 37.73/37.93  thf('175', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 37.73/37.93  thf('176', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 37.73/37.93  thf('177', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('178', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('179', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('180', plain,
% 37.73/37.93      (![X5 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 37.73/37.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 37.73/37.93  thf('181', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf('182', plain,
% 37.73/37.93      (![X18 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X18)
% 37.73/37.93          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 37.73/37.93          | ~ (v1_funct_1 @ X18)
% 37.73/37.93          | ~ (v1_relat_1 @ X18))),
% 37.73/37.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 37.73/37.93  thf('183', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0)))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['181', '182'])).
% 37.73/37.93  thf('184', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k2_relat_1 @ X0) = (k1_relat_1 @ (k4_relat_1 @ X0))))),
% 37.73/37.93      inference('simplify', [status(thm)], ['183'])).
% 37.73/37.93  thf('185', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['180', '184'])).
% 37.73/37.93  thf('186', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['179', '185'])).
% 37.73/37.93  thf('187', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k2_relat_1 @ (k4_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('simplify', [status(thm)], ['186'])).
% 37.73/37.93  thf('188', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93            = (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['178', '187'])).
% 37.73/37.93  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('190', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('192', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('193', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('demod', [status(thm)], ['188', '189', '190', '191', '192'])).
% 37.73/37.93  thf('194', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['177', '193'])).
% 37.73/37.93  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('196', plain,
% 37.73/37.93      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['194', '195'])).
% 37.73/37.93  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('199', plain,
% 37.73/37.93      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 37.73/37.93        | (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)],
% 37.73/37.93                ['171', '174', '175', '176', '196', '197', '198'])).
% 37.73/37.93  thf('200', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('simplify', [status(thm)], ['199'])).
% 37.73/37.93  thf('201', plain,
% 37.73/37.93      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['194', '195'])).
% 37.73/37.93  thf('202', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('203', plain,
% 37.73/37.93      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['194', '195'])).
% 37.73/37.93  thf('204', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('205', plain,
% 37.73/37.93      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ 
% 37.73/37.93          (k4_relat_1 @ sk_C)) = (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['203', '204'])).
% 37.73/37.93  thf('206', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ 
% 37.73/37.93            (k4_relat_1 @ sk_C)) = (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['202', '205'])).
% 37.73/37.93  thf('207', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('208', plain,
% 37.73/37.93      (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ (k4_relat_1 @ sk_C))
% 37.73/37.93         = (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['206', '207'])).
% 37.73/37.93  thf('209', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf(dt_k2_funct_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.73/37.93       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 37.73/37.93         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 37.73/37.93  thf('210', plain,
% 37.73/37.93      (![X13 : $i]:
% 37.73/37.93         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 37.73/37.93          | ~ (v1_funct_1 @ X13)
% 37.73/37.93          | ~ (v1_relat_1 @ X13))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 37.73/37.93  thf('211', plain,
% 37.73/37.93      (![X18 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X18)
% 37.73/37.93          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 37.73/37.93          | ~ (v1_funct_1 @ X18)
% 37.73/37.93          | ~ (v1_relat_1 @ X18))),
% 37.73/37.93      inference('cnf', [status(esa)], [t55_funct_1])).
% 37.73/37.93  thf('212', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('213', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 37.73/37.93            = (k2_funct_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['211', '212'])).
% 37.73/37.93  thf('214', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 37.73/37.93              (k2_funct_1 @ X0)) = (k2_funct_1 @ X0)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['210', '213'])).
% 37.73/37.93  thf('215', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 37.73/37.93            = (k2_funct_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('simplify', [status(thm)], ['214'])).
% 37.73/37.93  thf('216', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 37.73/37.93            = (k2_funct_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['209', '215'])).
% 37.73/37.93  thf('217', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 37.73/37.93              (k4_relat_1 @ X0)) = (k2_funct_1 @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['216'])).
% 37.73/37.93  thf('218', plain,
% 37.73/37.93      ((((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup+', [status(thm)], ['208', '217'])).
% 37.73/37.93  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('222', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 37.73/37.93  thf(t59_funct_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 37.73/37.93       ( ( v2_funct_1 @ A ) =>
% 37.73/37.93         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 37.73/37.93             ( k2_relat_1 @ A ) ) & 
% 37.73/37.93           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 37.73/37.93             ( k2_relat_1 @ A ) ) ) ) ))).
% 37.73/37.93  thf('223', plain,
% 37.73/37.93      (![X20 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X20)
% 37.73/37.93          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X20) @ X20))
% 37.73/37.93              = (k2_relat_1 @ X20))
% 37.73/37.93          | ~ (v1_funct_1 @ X20)
% 37.73/37.93          | ~ (v1_relat_1 @ X20))),
% 37.73/37.93      inference('cnf', [status(esa)], [t59_funct_1])).
% 37.73/37.93  thf('224', plain,
% 37.73/37.93      ((((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C))
% 37.73/37.93          = (k2_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup+', [status(thm)], ['222', '223'])).
% 37.73/37.93  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('228', plain,
% 37.73/37.93      (((k2_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C))
% 37.73/37.93         = (k2_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 37.73/37.93  thf('229', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('230', plain,
% 37.73/37.93      (![X56 : $i, X57 : $i, X58 : $i]:
% 37.73/37.93         (((X56) = (k1_xboole_0))
% 37.73/37.93          | ~ (v1_funct_1 @ X57)
% 37.73/37.93          | ~ (v1_funct_2 @ X57 @ X58 @ X56)
% 37.73/37.93          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X56)))
% 37.73/37.93          | ((k5_relat_1 @ (k2_funct_1 @ X57) @ X57) = (k6_partfun1 @ X56))
% 37.73/37.93          | ~ (v2_funct_1 @ X57)
% 37.73/37.93          | ((k2_relset_1 @ X58 @ X56 @ X57) != (X56)))),
% 37.73/37.93      inference('cnf', [status(esa)], [t35_funct_2])).
% 37.73/37.93  thf('231', plain,
% 37.73/37.93      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C)
% 37.73/37.93        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 37.73/37.93        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ((sk_B) = (k1_xboole_0)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['229', '230'])).
% 37.73/37.93  thf('232', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('234', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 37.73/37.93  thf('235', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('236', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('237', plain,
% 37.73/37.93      ((((sk_B) != (sk_B))
% 37.73/37.93        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 37.73/37.93        | ((sk_B) = (k1_xboole_0)))),
% 37.73/37.93      inference('demod', [status(thm)],
% 37.73/37.93                ['231', '232', '233', '234', '235', '236'])).
% 37.73/37.93  thf('238', plain,
% 37.73/37.93      ((((sk_B) = (k1_xboole_0))
% 37.73/37.93        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['237'])).
% 37.73/37.93  thf('239', plain, (((sk_B) != (k1_xboole_0))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('240', plain,
% 37.73/37.93      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 37.73/37.93      inference('simplify_reflect-', [status(thm)], ['238', '239'])).
% 37.73/37.93  thf(t71_relat_1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 37.73/37.93       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 37.73/37.93  thf('241', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 37.73/37.93      inference('cnf', [status(esa)], [t71_relat_1])).
% 37.73/37.93  thf('242', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 37.73/37.93  thf('243', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X9)) = (X9))),
% 37.73/37.93      inference('demod', [status(thm)], ['241', '242'])).
% 37.73/37.93  thf('244', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['228', '240', '243'])).
% 37.73/37.93  thf('245', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['201', '244'])).
% 37.73/37.93  thf('246', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['134', '135'])).
% 37.73/37.93  thf('247', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('demod', [status(thm)], ['37', '38'])).
% 37.73/37.93  thf('248', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 37.73/37.93              (k4_relat_1 @ X0)) = (k2_funct_1 @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['216'])).
% 37.73/37.93  thf('249', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 37.73/37.93            = (k2_funct_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['247', '248'])).
% 37.73/37.93  thf('250', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 37.73/37.93              = (k2_funct_1 @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['249'])).
% 37.73/37.93  thf('251', plain,
% 37.73/37.93      ((((k4_relat_1 @ 
% 37.73/37.93          (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 37.73/37.93          = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['246', '250'])).
% 37.73/37.93  thf('252', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('253', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('254', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k4_relat_1 @ X1)))
% 37.73/37.93          | ~ (v1_relat_1 @ X1))),
% 37.73/37.93      inference('demod', [status(thm)], ['37', '38'])).
% 37.73/37.93  thf('255', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('256', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ 
% 37.73/37.93            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))))
% 37.73/37.93            = (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['254', '255'])).
% 37.73/37.93  thf('257', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('258', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k5_relat_1 @ X0 @ 
% 37.73/37.93               (k6_partfun1 @ (k1_relat_1 @ (k4_relat_1 @ X0)))))
% 37.73/37.93              = (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('clc', [status(thm)], ['256', '257'])).
% 37.73/37.93  thf('259', plain,
% 37.73/37.93      ((((k4_relat_1 @ 
% 37.73/37.93          (k5_relat_1 @ (k4_relat_1 @ sk_C) @ 
% 37.73/37.93           (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 37.73/37.93          = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['253', '258'])).
% 37.73/37.93  thf('260', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['54', '61', '64'])).
% 37.73/37.93  thf('261', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('262', plain,
% 37.73/37.93      ((((k4_relat_1 @ 
% 37.73/37.93          (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))) = (
% 37.73/37.93          sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['259', '260', '261'])).
% 37.73/37.93  thf('263', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ((k4_relat_1 @ 
% 37.73/37.93            (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))) = (
% 37.73/37.93            sk_C)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['252', '262'])).
% 37.73/37.93  thf('264', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('265', plain,
% 37.73/37.93      (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 37.73/37.93         = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['263', '264'])).
% 37.73/37.93  thf('266', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 37.73/37.93  thf('267', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 37.73/37.93  thf('268', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('simplify', [status(thm)], ['199'])).
% 37.73/37.93  thf('269', plain, (((sk_C) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 37.73/37.93      inference('demod', [status(thm)], ['251', '265', '266', '267', '268'])).
% 37.73/37.93  thf('270', plain,
% 37.73/37.93      ((((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) != (k6_partfun1 @ sk_A))
% 37.73/37.93        | ((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B))
% 37.73/37.93        | ((k4_relat_1 @ sk_D) = (sk_C))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('demod', [status(thm)],
% 37.73/37.93                ['115', '136', '137', '152', '200', '245', '269'])).
% 37.73/37.93  thf('271', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('272', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('273', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('274', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['43'])).
% 37.73/37.93  thf('275', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['273', '274'])).
% 37.73/37.93  thf('276', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['275'])).
% 37.73/37.93  thf('277', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['43'])).
% 37.73/37.93  thf('278', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['276', '277'])).
% 37.73/37.93  thf('279', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['278'])).
% 37.73/37.93  thf('280', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('281', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['278'])).
% 37.73/37.93  thf('282', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['43'])).
% 37.73/37.93  thf('283', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ 
% 37.73/37.93            (k4_relat_1 @ 
% 37.73/37.93             (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 37.73/37.93            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['281', '282'])).
% 37.73/37.93  thf('284', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ 
% 37.73/37.93               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['283'])).
% 37.73/37.93  thf('285', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ 
% 37.73/37.93            (k4_relat_1 @ 
% 37.73/37.93             (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 37.73/37.93            = (X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['280', '284'])).
% 37.73/37.93  thf('286', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ 
% 37.73/37.93               (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))
% 37.73/37.93              = (X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['285'])).
% 37.73/37.93  thf('287', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k4_relat_1 @ 
% 37.73/37.93            (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))
% 37.73/37.93            = (X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['279', '286'])).
% 37.73/37.93  thf('288', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ 
% 37.73/37.93               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))
% 37.73/37.93              = (X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['287'])).
% 37.73/37.93  thf('289', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['278'])).
% 37.73/37.93  thf('290', plain,
% 37.73/37.93      (![X11 : $i]:
% 37.73/37.93         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X11)) @ X11) = (X11))
% 37.73/37.93          | ~ (v1_relat_1 @ X11))),
% 37.73/37.93      inference('demod', [status(thm)], ['14', '15'])).
% 37.73/37.93  thf('291', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ 
% 37.73/37.93              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))
% 37.73/37.93              = (k5_relat_1 @ (k6_partfun1 @ X1) @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['43'])).
% 37.73/37.93  thf('292', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('293', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ 
% 37.73/37.93               (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ X0))))),
% 37.73/37.93      inference('sup+', [status(thm)], ['291', '292'])).
% 37.73/37.93  thf('294', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['290', '293'])).
% 37.73/37.93  thf('295', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['294'])).
% 37.73/37.93  thf('296', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('297', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('clc', [status(thm)], ['295', '296'])).
% 37.73/37.93  thf('298', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         ((v1_relat_1 @ 
% 37.73/37.93           (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['289', '297'])).
% 37.73/37.93  thf('299', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | (v1_relat_1 @ 
% 37.73/37.93             (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))))),
% 37.73/37.93      inference('simplify', [status(thm)], ['298'])).
% 37.73/37.93  thf('300', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ 
% 37.73/37.93               (k4_relat_1 @ 
% 37.73/37.93                (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))))),
% 37.73/37.93      inference('sup+', [status(thm)], ['288', '299'])).
% 37.73/37.93  thf('301', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['272', '300'])).
% 37.73/37.93  thf('302', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 37.73/37.93      inference('clc', [status(thm)], ['295', '296'])).
% 37.73/37.93  thf('303', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         ((v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0))))
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('clc', [status(thm)], ['301', '302'])).
% 37.73/37.93  thf('304', plain,
% 37.73/37.93      (((v1_relat_1 @ (k4_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 37.73/37.93      inference('sup+', [status(thm)], ['271', '303'])).
% 37.73/37.93  thf('305', plain, ((v1_relat_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['20', '21'])).
% 37.73/37.93  thf('306', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['304', '305'])).
% 37.73/37.93  thf('307', plain,
% 37.73/37.93      ((((k4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) != (k6_partfun1 @ sk_A))
% 37.73/37.93        | ((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B))
% 37.73/37.93        | ((k4_relat_1 @ sk_D) = (sk_C))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('demod', [status(thm)], ['270', '306'])).
% 37.73/37.93  thf('308', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('309', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(redefinition_k1_partfun1, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 37.73/37.93     ( ( ( v1_funct_1 @ E ) & 
% 37.73/37.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 37.73/37.93         ( v1_funct_1 @ F ) & 
% 37.73/37.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 37.73/37.93       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 37.73/37.93  thf('310', plain,
% 37.73/37.93      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 37.73/37.93         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 37.73/37.93          | ~ (v1_funct_1 @ X46)
% 37.73/37.93          | ~ (v1_funct_1 @ X49)
% 37.73/37.93          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 37.73/37.93          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 37.73/37.93              = (k5_relat_1 @ X46 @ X49)))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 37.73/37.93  thf('311', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.73/37.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 37.73/37.93            = (k5_relat_1 @ sk_C @ X0))
% 37.73/37.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['309', '310'])).
% 37.73/37.93  thf('312', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('313', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.73/37.93         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 37.73/37.93            = (k5_relat_1 @ sk_C @ X0))
% 37.73/37.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 37.73/37.93          | ~ (v1_funct_1 @ X0))),
% 37.73/37.93      inference('demod', [status(thm)], ['311', '312'])).
% 37.73/37.93  thf('314', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ sk_D)
% 37.73/37.93        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.73/37.93            = (k5_relat_1 @ sk_C @ sk_D)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['308', '313'])).
% 37.73/37.93  thf('315', plain, ((v1_funct_1 @ sk_D)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('316', plain,
% 37.73/37.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 37.73/37.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 37.73/37.93        (k6_partfun1 @ sk_A))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('317', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('318', plain,
% 37.73/37.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf(dt_k1_partfun1, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 37.73/37.93     ( ( ( v1_funct_1 @ E ) & 
% 37.73/37.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 37.73/37.93         ( v1_funct_1 @ F ) & 
% 37.73/37.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 37.73/37.93       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 37.73/37.93         ( m1_subset_1 @
% 37.73/37.93           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 37.73/37.93           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 37.73/37.93  thf('319', plain,
% 37.73/37.93      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 37.73/37.93         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 37.73/37.93          | ~ (v1_funct_1 @ X38)
% 37.73/37.93          | ~ (v1_funct_1 @ X41)
% 37.73/37.93          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 37.73/37.93          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 37.73/37.93             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 37.73/37.93  thf('320', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.73/37.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 37.73/37.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 37.73/37.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 37.73/37.93          | ~ (v1_funct_1 @ X1)
% 37.73/37.93          | ~ (v1_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['318', '319'])).
% 37.73/37.93  thf('321', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('322', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 37.73/37.93         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 37.73/37.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 37.73/37.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 37.73/37.93          | ~ (v1_funct_1 @ X1))),
% 37.73/37.93      inference('demod', [status(thm)], ['320', '321'])).
% 37.73/37.93  thf('323', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ sk_D)
% 37.73/37.93        | (m1_subset_1 @ 
% 37.73/37.93           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 37.73/37.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['317', '322'])).
% 37.73/37.93  thf('324', plain, ((v1_funct_1 @ sk_D)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('325', plain,
% 37.73/37.93      ((m1_subset_1 @ 
% 37.73/37.93        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 37.73/37.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 37.73/37.93      inference('demod', [status(thm)], ['323', '324'])).
% 37.73/37.93  thf(redefinition_r2_relset_1, axiom,
% 37.73/37.93    (![A:$i,B:$i,C:$i,D:$i]:
% 37.73/37.93     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 37.73/37.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 37.73/37.93       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 37.73/37.93  thf('326', plain,
% 37.73/37.93      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 37.73/37.93         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 37.73/37.93          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 37.73/37.93          | ((X26) = (X29))
% 37.73/37.93          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 37.73/37.93      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 37.73/37.93  thf('327', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 37.73/37.93             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 37.73/37.93          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 37.73/37.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['325', '326'])).
% 37.73/37.93  thf('328', plain,
% 37.73/37.93      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 37.73/37.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 37.73/37.93        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.73/37.93            = (k6_partfun1 @ sk_A)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['316', '327'])).
% 37.73/37.93  thf(dt_k6_partfun1, axiom,
% 37.73/37.93    (![A:$i]:
% 37.73/37.93     ( ( m1_subset_1 @
% 37.73/37.93         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 37.73/37.93       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 37.73/37.93  thf('329', plain,
% 37.73/37.93      (![X45 : $i]:
% 37.73/37.93         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 37.73/37.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 37.73/37.93  thf('330', plain,
% 37.73/37.93      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 37.73/37.93         = (k6_partfun1 @ sk_A))),
% 37.73/37.93      inference('demod', [status(thm)], ['328', '329'])).
% 37.73/37.93  thf('331', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['314', '315', '330'])).
% 37.73/37.93  thf('332', plain,
% 37.73/37.93      (![X10 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X10)) = (k6_partfun1 @ X10))),
% 37.73/37.93      inference('demod', [status(thm)], ['24', '25', '26'])).
% 37.73/37.93  thf('333', plain,
% 37.73/37.93      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 37.73/37.93        | ((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B))
% 37.73/37.93        | ((k4_relat_1 @ sk_D) = (sk_C))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('demod', [status(thm)], ['307', '331', '332'])).
% 37.73/37.93  thf('334', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ((k4_relat_1 @ sk_D) = (sk_C))
% 37.73/37.93        | ((k2_relat_1 @ (k4_relat_1 @ sk_D)) != (sk_B)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['333'])).
% 37.73/37.93  thf('335', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('336', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('337', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('338', plain,
% 37.73/37.93      (![X5 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 37.73/37.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 37.73/37.93  thf('339', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf('340', plain,
% 37.73/37.93      (![X13 : $i]:
% 37.73/37.93         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 37.73/37.93          | ~ (v1_funct_1 @ X13)
% 37.73/37.93          | ~ (v1_relat_1 @ X13))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 37.73/37.93  thf('341', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         ((v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0))),
% 37.73/37.93      inference('sup+', [status(thm)], ['339', '340'])).
% 37.73/37.93  thf('342', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | (v1_funct_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['341'])).
% 37.73/37.93  thf('343', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         ((v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['338', '342'])).
% 37.73/37.93  thf('344', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | (v1_funct_1 @ X0))),
% 37.73/37.93      inference('sup-', [status(thm)], ['337', '343'])).
% 37.73/37.93  thf('345', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         ((v1_funct_1 @ X0)
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('simplify', [status(thm)], ['344'])).
% 37.73/37.93  thf('346', plain,
% 37.73/37.93      ((~ (v2_funct_1 @ sk_D)
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 37.73/37.93        | (v1_funct_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['336', '345'])).
% 37.73/37.93  thf('347', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('348', plain, ((v1_funct_1 @ sk_D)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('349', plain,
% 37.73/37.93      ((~ (v2_funct_1 @ sk_D)
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | (v1_funct_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('demod', [status(thm)], ['346', '347', '348'])).
% 37.73/37.93  thf('350', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ sk_D)
% 37.73/37.93        | (v1_funct_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ~ (v2_funct_1 @ sk_D))),
% 37.73/37.93      inference('sup-', [status(thm)], ['335', '349'])).
% 37.73/37.93  thf('351', plain, ((v1_relat_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['20', '21'])).
% 37.73/37.93  thf('352', plain,
% 37.73/37.93      (((v1_funct_1 @ (k4_relat_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['350', '351'])).
% 37.73/37.93  thf('353', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 37.73/37.93  thf('354', plain,
% 37.73/37.93      (![X5 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k4_relat_1 @ X5)) = (X5)) | ~ (v1_relat_1 @ X5))),
% 37.73/37.93      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 37.73/37.93  thf('355', plain,
% 37.73/37.93      (![X6 : $i, X7 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X6)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 37.73/37.93              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 37.73/37.93          | ~ (v1_relat_1 @ X7))),
% 37.73/37.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 37.73/37.93  thf('356', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 37.73/37.93            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ X1)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup+', [status(thm)], ['354', '355'])).
% 37.73/37.93  thf('357', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ sk_C)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93              = (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['353', '356'])).
% 37.73/37.93  thf('358', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('359', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X0)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93              = (k5_relat_1 @ sk_C @ (k4_relat_1 @ X0))))),
% 37.73/37.93      inference('demod', [status(thm)], ['357', '358'])).
% 37.73/37.93  thf('360', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('361', plain,
% 37.73/37.93      (![X6 : $i, X7 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X6)
% 37.73/37.93          | ((k4_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 37.73/37.93              = (k5_relat_1 @ (k4_relat_1 @ X6) @ (k4_relat_1 @ X7)))
% 37.73/37.93          | ~ (v1_relat_1 @ X7))),
% 37.73/37.93      inference('cnf', [status(esa)], [t54_relat_1])).
% 37.73/37.93  thf('362', plain,
% 37.73/37.93      (![X16 : $i, X17 : $i]:
% 37.73/37.93         (~ (v1_relat_1 @ X16)
% 37.73/37.93          | ~ (v1_funct_1 @ X16)
% 37.73/37.93          | (v2_funct_1 @ X17)
% 37.73/37.93          | ((k2_relat_1 @ X16) != (k1_relat_1 @ X17))
% 37.73/37.93          | ~ (v2_funct_1 @ (k5_relat_1 @ X16 @ X17))
% 37.73/37.93          | ~ (v1_funct_1 @ X17)
% 37.73/37.93          | ~ (v1_relat_1 @ X17))),
% 37.73/37.93      inference('cnf', [status(esa)], [t48_funct_1])).
% 37.73/37.93  thf('363', plain,
% 37.73/37.93      (![X0 : $i, X1 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 37.73/37.93          | ~ (v1_relat_1 @ X1)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X1))
% 37.73/37.93          | ((k2_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93              != (k1_relat_1 @ (k4_relat_1 @ X1)))
% 37.73/37.93          | (v2_funct_1 @ (k4_relat_1 @ X1))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['361', '362'])).
% 37.73/37.93  thf('364', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k2_relat_1 @ (k4_relat_1 @ X0)) != (k1_relat_1 @ sk_D))
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93          | ~ (v2_funct_1 @ 
% 37.73/37.93               (k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ X0))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['360', '363'])).
% 37.73/37.93  thf('365', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['2', '9', '12'])).
% 37.73/37.93  thf('366', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('367', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('368', plain, ((v1_funct_1 @ sk_D)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('369', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('370', plain, ((v1_relat_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['20', '21'])).
% 37.73/37.93  thf('371', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['304', '305'])).
% 37.73/37.93  thf('372', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k2_relat_1 @ (k4_relat_1 @ X0)) != (sk_B))
% 37.73/37.93          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | (v2_funct_1 @ sk_D)
% 37.73/37.93          | ~ (v1_relat_1 @ X0)
% 37.73/37.93          | ~ (v2_funct_1 @ 
% 37.73/37.93               (k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ sk_D) @ X0))))),
% 37.73/37.93      inference('demod', [status(thm)],
% 37.73/37.93                ['364', '365', '366', '367', '368', '369', '370', '371'])).
% 37.73/37.93  thf('373', plain,
% 37.73/37.93      ((~ (v2_funct_1 @ 
% 37.73/37.93           (k5_relat_1 @ sk_C @ (k4_relat_1 @ (k4_relat_1 @ sk_D))))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 37.73/37.93        | (v2_funct_1 @ sk_D)
% 37.73/37.93        | ~ (v1_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 37.73/37.93        | ((k2_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) != (sk_B)))),
% 37.73/37.93      inference('sup-', [status(thm)], ['359', '372'])).
% 37.73/37.93  thf('374', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('375', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['304', '305'])).
% 37.73/37.93  thf('376', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 37.73/37.93  thf('377', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('378', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('379', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('380', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('381', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['75', '76', '77'])).
% 37.73/37.93  thf('382', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['228', '240', '243'])).
% 37.73/37.93  thf('383', plain,
% 37.73/37.93      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 37.73/37.93        | (v2_funct_1 @ sk_D)
% 37.73/37.93        | ((sk_B) != (sk_B)))),
% 37.73/37.93      inference('demod', [status(thm)],
% 37.73/37.93                ['373', '374', '375', '376', '377', '378', '379', '380', 
% 37.73/37.93                 '381', '382'])).
% 37.73/37.93  thf('384', plain,
% 37.73/37.93      (((v2_funct_1 @ sk_D) | ~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 37.73/37.93      inference('simplify', [status(thm)], ['383'])).
% 37.73/37.93  thf('385', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['314', '315', '330'])).
% 37.73/37.93  thf('386', plain, (![X15 : $i]: (v2_funct_1 @ (k6_partfun1 @ X15))),
% 37.73/37.93      inference('demod', [status(thm)], ['172', '173'])).
% 37.73/37.93  thf('387', plain, ((v2_funct_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['384', '385', '386'])).
% 37.73/37.93  thf('388', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['352', '387'])).
% 37.73/37.93  thf('389', plain,
% 37.73/37.93      (![X2 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X2)) | ~ (v1_relat_1 @ X2))),
% 37.73/37.93      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 37.73/37.93  thf('390', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('391', plain,
% 37.73/37.93      (![X0 : $i]:
% 37.73/37.93         (((k1_relat_1 @ (k4_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v2_funct_1 @ (k4_relat_1 @ X0))
% 37.73/37.93          | ~ (v1_relat_1 @ X0))),
% 37.73/37.93      inference('simplify', [status(thm)], ['125'])).
% 37.73/37.93  thf('392', plain,
% 37.73/37.93      ((~ (v1_funct_1 @ sk_D)
% 37.73/37.93        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ~ (v2_funct_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 37.73/37.93        | ((k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_D)))
% 37.73/37.93            = (k2_relat_1 @ (k4_relat_1 @ sk_D))))),
% 37.73/37.93      inference('sup-', [status(thm)], ['390', '391'])).
% 37.73/37.93  thf('393', plain, ((v1_funct_1 @ sk_D)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('394', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('395', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_D)) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['45', '46', '47'])).
% 37.73/37.93  thf('396', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['2', '9', '12'])).
% 37.73/37.93  thf('397', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_D))
% 37.73/37.93        | ~ (v2_funct_1 @ sk_D)
% 37.73/37.93        | ((sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_D))))),
% 37.73/37.93      inference('demod', [status(thm)], ['392', '393', '394', '395', '396'])).
% 37.73/37.93  thf('398', plain,
% 37.73/37.93      ((~ (v1_relat_1 @ sk_D)
% 37.73/37.93        | ((sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))
% 37.73/37.93        | ~ (v2_funct_1 @ sk_D))),
% 37.73/37.93      inference('sup-', [status(thm)], ['389', '397'])).
% 37.73/37.93  thf('399', plain, ((v1_relat_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['20', '21'])).
% 37.73/37.93  thf('400', plain,
% 37.73/37.93      ((((sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_D))) | ~ (v2_funct_1 @ sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['398', '399'])).
% 37.73/37.93  thf('401', plain, ((v2_funct_1 @ sk_D)),
% 37.73/37.93      inference('demod', [status(thm)], ['384', '385', '386'])).
% 37.73/37.93  thf('402', plain, (((sk_B) = (k2_relat_1 @ (k4_relat_1 @ sk_D)))),
% 37.73/37.93      inference('demod', [status(thm)], ['400', '401'])).
% 37.73/37.93  thf('403', plain, ((((k4_relat_1 @ sk_D) = (sk_C)) | ((sk_B) != (sk_B)))),
% 37.73/37.93      inference('demod', [status(thm)], ['334', '388', '402'])).
% 37.73/37.93  thf('404', plain, (((k4_relat_1 @ sk_D) = (sk_C))),
% 37.73/37.93      inference('simplify', [status(thm)], ['403'])).
% 37.73/37.93  thf('405', plain, (((k4_relat_1 @ sk_C) = (sk_D))),
% 37.73/37.93      inference('demod', [status(thm)], ['48', '404'])).
% 37.73/37.93  thf('406', plain,
% 37.73/37.93      (![X12 : $i]:
% 37.73/37.93         (~ (v2_funct_1 @ X12)
% 37.73/37.93          | ((k2_funct_1 @ X12) = (k4_relat_1 @ X12))
% 37.73/37.93          | ~ (v1_funct_1 @ X12)
% 37.73/37.93          | ~ (v1_relat_1 @ X12))),
% 37.73/37.93      inference('cnf', [status(esa)], [d9_funct_1])).
% 37.73/37.93  thf('407', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('408', plain,
% 37.73/37.93      ((((sk_D) != (k4_relat_1 @ sk_C))
% 37.73/37.93        | ~ (v1_relat_1 @ sk_C)
% 37.73/37.93        | ~ (v1_funct_1 @ sk_C)
% 37.73/37.93        | ~ (v2_funct_1 @ sk_C))),
% 37.73/37.93      inference('sup-', [status(thm)], ['406', '407'])).
% 37.73/37.93  thf('409', plain, ((v1_relat_1 @ sk_C)),
% 37.73/37.93      inference('demod', [status(thm)], ['70', '71'])).
% 37.73/37.93  thf('410', plain, ((v1_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('411', plain, ((v2_funct_1 @ sk_C)),
% 37.73/37.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 37.73/37.93  thf('412', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 37.73/37.93      inference('demod', [status(thm)], ['408', '409', '410', '411'])).
% 37.73/37.93  thf('413', plain, ($false),
% 37.73/37.93      inference('simplify_reflect-', [status(thm)], ['405', '412'])).
% 37.73/37.93  
% 37.73/37.93  % SZS output end Refutation
% 37.73/37.93  
% 37.73/37.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

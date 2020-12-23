%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0980+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rCw5zT3Xqm

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:49 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 984 expanded)
%              Number of leaves         :   36 ( 271 expanded)
%              Depth                    :   24
%              Number of atoms          : 1574 (19353 expanded)
%              Number of equality atoms :  164 (1369 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t26_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
             => ( ( ( C = k1_xboole_0 )
                  & ( B != k1_xboole_0 ) )
                | ( v2_funct_1 @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('2',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_C = X1 )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_2 @ X7 @ X5 @ X6 )
      | ( X5
        = ( k1_relset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X0 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_B
          = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','28'])).

thf('30',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k1_relat_1 @ sk_E ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_E ) )
      | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('34',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(t47_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) )
           => ( v2_funct_1 @ B ) ) ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v2_funct_1 @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','39','40'])).

thf('42',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('51',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf('52',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('55',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ( sk_B
        = ( k1_relat_1 @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( zip_tseitin_0 @ X8 @ X9 )
      | ( zip_tseitin_1 @ X10 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,
    ( ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('62',plain,(
    ! [X3: $i] :
      ( zip_tseitin_0 @ X3 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('65',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','63','64'])).

thf('66',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v2_funct_1 @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ ( k1_relat_1 @ X30 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X29 @ X30 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_funct_1])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_E )
        | ~ ( v1_funct_1 @ sk_E )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['37','38'])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ k1_xboole_0 )
        | ~ ( v2_funct_1 @ ( k5_relat_1 @ X0 @ sk_E ) )
        | ( v2_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['43','44'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v2_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_funct_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 != k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('85',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('89',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('90',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k1_partfun1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 )
        = ( k5_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('91',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ sk_D ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( sk_D = k1_xboole_0 )
        | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ X2 @ X1 @ sk_D @ X0 )
          = ( k5_relat_1 @ sk_D @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('97',plain,
    ( ( ( ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E )
        = ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('99',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('100',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('103',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( v2_funct_1 @ ( k1_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,
    ( ( ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','104'])).

thf('106',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('108',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','108'])).

thf('110',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ sk_D @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('111',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('112',plain,
    ( ( v2_funct_1 @ ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('115',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('116',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k1_partfun1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 )
        = ( k5_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('118',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ k1_xboole_0 @ X0 )
          = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_funct_1 @ k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('120',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ X2 @ X1 @ k1_xboole_0 @ X0 )
          = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','121'])).

thf('123',plain,
    ( ( ~ ( v1_funct_1 @ sk_E )
      | ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ sk_B @ sk_C @ k1_xboole_0 @ sk_E )
        = ( k5_relat_1 @ k1_xboole_0 @ sk_E ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('126',plain,
    ( ( ( k1_partfun1 @ sk_A @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 @ sk_E )
      = ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ k1_xboole_0 @ sk_E ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','126'])).

thf('128',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['109','127'])).

thf('129',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('130',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['128','129'])).

thf('131',plain,(
    ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(simpl_trail,[status(thm)],['49','130'])).

thf('132',plain,(
    v2_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k1_partfun1 @ X15 @ X16 @ X18 @ X19 @ X14 @ X17 )
        = ( k5_relat_1 @ X14 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['132','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['131','142'])).


%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LfuUN5XNjm

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:42 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 146 expanded)
%              Number of leaves         :   38 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  919 (2793 expanded)
%              Number of equality atoms :   61 ( 207 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( m1_subset_1 @ ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k4_relset_1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 )
        = ( k5_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
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

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('18',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['15','22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['40','42','47','52'])).

thf('54',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['12','53'])).

thf('55',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('58',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( ( k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38 )
        = ( k5_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['55','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LfuUN5XNjm
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:00:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 439 iterations in 0.507s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.96  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.96  thf(sk_E_type, type, sk_E: $i).
% 0.75/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.96  thf(t20_funct_2, conjecture,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ![E:$i]:
% 0.75/0.96         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.75/0.96             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.75/0.96           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.75/0.96               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.75/0.96             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.75/0.96               ( ( k2_relset_1 @
% 0.75/0.96                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.75/0.96                 ( C ) ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.75/0.96            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96          ( ![E:$i]:
% 0.75/0.96            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.75/0.96                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.75/0.96              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.75/0.96                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.75/0.96                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.75/0.96                  ( ( k2_relset_1 @
% 0.75/0.96                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.75/0.96                    ( C ) ) ) ) ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('1', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(dt_k4_relset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.96     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.96       ( m1_subset_1 @
% 0.75/0.96         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.75/0.96         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 0.75/0.96  thf('2', plain,
% 0.75/0.96      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.75/0.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.75/0.96          | (m1_subset_1 @ (k4_relset_1 @ X10 @ X11 @ X13 @ X14 @ X9 @ X12) @ 
% 0.75/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X14))))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.75/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      ((m1_subset_1 @ 
% 0.75/0.96        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.75/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['0', '3'])).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k4_relset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.96     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.96       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.75/0.96  thf('7', plain,
% 0.75/0.96      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.75/0.96          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.75/0.96          | ((k4_relset_1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24)
% 0.75/0.96              = (k5_relat_1 @ X21 @ X24)))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.75/0.96  thf('8', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.75/0.96            = (k5_relat_1 @ sk_D @ X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.96  thf('9', plain,
% 0.75/0.96      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.75/0.96         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.75/0.96      inference('sup-', [status(thm)], ['5', '8'])).
% 0.75/0.96  thf('10', plain,
% 0.75/0.96      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.75/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.75/0.96      inference('demod', [status(thm)], ['4', '9'])).
% 0.75/0.96  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.75/0.96         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.75/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.96  thf('12', plain,
% 0.75/0.96      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 0.75/0.96         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.96  thf('13', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(d1_funct_2, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_1, axiom,
% 0.75/0.96    (![C:$i,B:$i,A:$i]:
% 0.75/0.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.96  thf('14', plain,
% 0.75/0.96      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.96         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.75/0.96          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.75/0.96          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 0.75/0.96        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.96  thf(zf_stmt_2, axiom,
% 0.75/0.96    (![B:$i,A:$i]:
% 0.75/0.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.96       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.96  thf('16', plain,
% 0.75/0.96      (![X27 : $i, X28 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.96  thf('17', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.80/0.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.80/0.96  thf(zf_stmt_5, axiom,
% 0.80/0.96    (![A:$i,B:$i,C:$i]:
% 0.80/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/0.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.80/0.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.80/0.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.80/0.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.80/0.96  thf('18', plain,
% 0.80/0.96      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.80/0.96         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.80/0.96          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.80/0.96          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.80/0.96  thf('19', plain,
% 0.80/0.96      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.80/0.96      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/0.96  thf('20', plain,
% 0.80/0.96      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 0.80/0.96      inference('sup-', [status(thm)], ['16', '19'])).
% 0.80/0.96  thf('21', plain, (((sk_C) != (k1_xboole_0))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('22', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 0.80/0.96      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.80/0.96  thf('23', plain,
% 0.80/0.96      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf(redefinition_k1_relset_1, axiom,
% 0.80/0.96    (![A:$i,B:$i,C:$i]:
% 0.80/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.80/0.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.80/0.96  thf('24', plain,
% 0.80/0.96      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.80/0.96         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.80/0.96          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.80/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.80/0.96  thf('25', plain,
% 0.80/0.96      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.80/0.96      inference('sup-', [status(thm)], ['23', '24'])).
% 0.80/0.96  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 0.80/0.96      inference('demod', [status(thm)], ['15', '22', '25'])).
% 0.80/0.96  thf('27', plain,
% 0.80/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('28', plain,
% 0.80/0.96      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.80/0.96         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.80/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.80/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.80/0.96  thf('29', plain,
% 0.80/0.96      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.80/0.96      inference('sup-', [status(thm)], ['27', '28'])).
% 0.80/0.96  thf('30', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 0.80/0.96      inference('sup+', [status(thm)], ['29', '30'])).
% 0.80/0.96  thf(t47_relat_1, axiom,
% 0.80/0.96    (![A:$i]:
% 0.80/0.96     ( ( v1_relat_1 @ A ) =>
% 0.80/0.96       ( ![B:$i]:
% 0.80/0.96         ( ( v1_relat_1 @ B ) =>
% 0.80/0.96           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.80/0.96             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.80/0.96  thf('32', plain,
% 0.80/0.96      (![X7 : $i, X8 : $i]:
% 0.80/0.96         (~ (v1_relat_1 @ X7)
% 0.80/0.96          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8)) = (k2_relat_1 @ X8))
% 0.80/0.96          | ~ (r1_tarski @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X7))
% 0.80/0.96          | ~ (v1_relat_1 @ X8))),
% 0.80/0.96      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.80/0.96  thf('33', plain,
% 0.80/0.96      (![X0 : $i]:
% 0.80/0.96         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 0.80/0.96          | ~ (v1_relat_1 @ X0)
% 0.80/0.96          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 0.80/0.96          | ~ (v1_relat_1 @ sk_D))),
% 0.80/0.96      inference('sup-', [status(thm)], ['31', '32'])).
% 0.80/0.96  thf('34', plain,
% 0.80/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf(cc2_relat_1, axiom,
% 0.80/0.96    (![A:$i]:
% 0.80/0.96     ( ( v1_relat_1 @ A ) =>
% 0.80/0.96       ( ![B:$i]:
% 0.80/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.80/0.96  thf('35', plain,
% 0.80/0.96      (![X3 : $i, X4 : $i]:
% 0.80/0.96         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.80/0.96          | (v1_relat_1 @ X3)
% 0.80/0.96          | ~ (v1_relat_1 @ X4))),
% 0.80/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.80/0.96  thf('36', plain,
% 0.80/0.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.80/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.80/0.96  thf(fc6_relat_1, axiom,
% 0.80/0.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.80/0.96  thf('37', plain,
% 0.80/0.96      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.80/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/0.96  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.80/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.80/0.96  thf('39', plain,
% 0.80/0.96      (![X0 : $i]:
% 0.80/0.96         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 0.80/0.96          | ~ (v1_relat_1 @ X0)
% 0.80/0.96          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 0.80/0.96      inference('demod', [status(thm)], ['33', '38'])).
% 0.80/0.96  thf('40', plain,
% 0.80/0.96      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.80/0.96        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (k2_relat_1 @ sk_E))
% 0.80/0.96        | ~ (v1_relat_1 @ sk_E))),
% 0.80/0.96      inference('sup-', [status(thm)], ['26', '39'])).
% 0.80/0.96  thf(d10_xboole_0, axiom,
% 0.80/0.96    (![A:$i,B:$i]:
% 0.80/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.80/0.96  thf('41', plain,
% 0.80/0.96      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.80/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.80/0.96  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.80/0.96      inference('simplify', [status(thm)], ['41'])).
% 0.80/0.96  thf('43', plain,
% 0.80/0.96      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('44', plain,
% 0.80/0.96      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.80/0.96         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.80/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.80/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.80/0.96  thf('45', plain,
% 0.80/0.96      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 0.80/0.96      inference('sup-', [status(thm)], ['43', '44'])).
% 0.80/0.96  thf('46', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('47', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 0.80/0.96      inference('sup+', [status(thm)], ['45', '46'])).
% 0.80/0.96  thf('48', plain,
% 0.80/0.96      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('49', plain,
% 0.80/0.96      (![X3 : $i, X4 : $i]:
% 0.80/0.96         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.80/0.96          | (v1_relat_1 @ X3)
% 0.80/0.96          | ~ (v1_relat_1 @ X4))),
% 0.80/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.80/0.96  thf('50', plain,
% 0.80/0.96      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.80/0.96      inference('sup-', [status(thm)], ['48', '49'])).
% 0.80/0.96  thf('51', plain,
% 0.80/0.96      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.80/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.80/0.96  thf('52', plain, ((v1_relat_1 @ sk_E)),
% 0.80/0.96      inference('demod', [status(thm)], ['50', '51'])).
% 0.80/0.96  thf('53', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.80/0.96      inference('demod', [status(thm)], ['40', '42', '47', '52'])).
% 0.80/0.96  thf('54', plain,
% 0.80/0.96      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.80/0.96      inference('demod', [status(thm)], ['12', '53'])).
% 0.80/0.96  thf('55', plain,
% 0.80/0.96      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.80/0.96         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('56', plain,
% 0.80/0.96      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('57', plain,
% 0.80/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf(redefinition_k1_partfun1, axiom,
% 0.80/0.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.80/0.96     ( ( ( v1_funct_1 @ E ) & 
% 0.80/0.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.80/0.96         ( v1_funct_1 @ F ) & 
% 0.80/0.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.80/0.96       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.80/0.96  thf('58', plain,
% 0.80/0.96      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.80/0.96         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.80/0.96          | ~ (v1_funct_1 @ X35)
% 0.80/0.96          | ~ (v1_funct_1 @ X38)
% 0.80/0.96          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.80/0.96          | ((k1_partfun1 @ X36 @ X37 @ X39 @ X40 @ X35 @ X38)
% 0.80/0.96              = (k5_relat_1 @ X35 @ X38)))),
% 0.80/0.96      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.80/0.96  thf('59', plain,
% 0.80/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.80/0.96            = (k5_relat_1 @ sk_D @ X0))
% 0.80/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/0.96          | ~ (v1_funct_1 @ X0)
% 0.80/0.96          | ~ (v1_funct_1 @ sk_D))),
% 0.80/0.96      inference('sup-', [status(thm)], ['57', '58'])).
% 0.80/0.96  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('61', plain,
% 0.80/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/0.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.80/0.96            = (k5_relat_1 @ sk_D @ X0))
% 0.80/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.80/0.96          | ~ (v1_funct_1 @ X0))),
% 0.80/0.96      inference('demod', [status(thm)], ['59', '60'])).
% 0.80/0.96  thf('62', plain,
% 0.80/0.96      ((~ (v1_funct_1 @ sk_E)
% 0.80/0.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.80/0.96            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.80/0.96      inference('sup-', [status(thm)], ['56', '61'])).
% 0.80/0.96  thf('63', plain, ((v1_funct_1 @ sk_E)),
% 0.80/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/0.96  thf('64', plain,
% 0.80/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.80/0.96         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.80/0.96      inference('demod', [status(thm)], ['62', '63'])).
% 0.80/0.96  thf('65', plain,
% 0.80/0.96      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 0.80/0.96      inference('demod', [status(thm)], ['55', '64'])).
% 0.80/0.96  thf('66', plain, ($false),
% 0.80/0.96      inference('simplify_reflect-', [status(thm)], ['54', '65'])).
% 0.80/0.96  
% 0.80/0.96  % SZS output end Refutation
% 0.80/0.96  
% 0.80/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

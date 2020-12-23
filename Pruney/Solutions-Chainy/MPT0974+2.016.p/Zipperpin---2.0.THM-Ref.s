%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ETpjjsoCGR

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:42 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 175 expanded)
%              Number of leaves         :   41 (  70 expanded)
%              Depth                    :   10
%              Number of atoms          :  968 (3331 expanded)
%              Number of equality atoms :   60 ( 242 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

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
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( m1_subset_1 @ ( k4_relset_1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X16 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
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

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['29','30'])).

thf('49',plain,(
    r1_tarski @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['40','49','54','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['12','60'])).

thf('62',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ETpjjsoCGR
% 0.15/0.38  % Computer   : n015.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 16:53:38 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 1.07/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.26  % Solved by: fo/fo7.sh
% 1.07/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.26  % done 631 iterations in 0.771s
% 1.07/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.26  % SZS output start Refutation
% 1.07/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.26  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.26  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.26  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.07/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.26  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.07/1.26  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.26  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.26  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.07/1.26  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.26  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.26  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.07/1.26  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.07/1.26  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.26  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.26  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.26  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.07/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.26  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.26  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.26  thf(sk_E_type, type, sk_E: $i).
% 1.07/1.26  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.07/1.26  thf(t20_funct_2, conjecture,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.26         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26       ( ![E:$i]:
% 1.07/1.26         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.07/1.26             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.07/1.26           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.07/1.26               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.07/1.26             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.07/1.26               ( ( k2_relset_1 @
% 1.07/1.26                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.07/1.26                 ( C ) ) ) ) ) ) ))).
% 1.07/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.26    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.26        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.26            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.26          ( ![E:$i]:
% 1.07/1.26            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.07/1.26                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.07/1.26              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 1.07/1.26                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 1.07/1.26                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.07/1.26                  ( ( k2_relset_1 @
% 1.07/1.26                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.07/1.26                    ( C ) ) ) ) ) ) ) )),
% 1.07/1.26    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 1.07/1.26  thf('0', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('1', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(dt_k4_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.26     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.26       ( m1_subset_1 @
% 1.07/1.26         ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.07/1.26         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ))).
% 1.07/1.26  thf('2', plain,
% 1.07/1.26      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 1.07/1.26          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.07/1.26          | (m1_subset_1 @ (k4_relset_1 @ X12 @ X13 @ X15 @ X16 @ X11 @ X14) @ 
% 1.07/1.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X16))))),
% 1.07/1.26      inference('cnf', [status(esa)], [dt_k4_relset_1])).
% 1.07/1.26  thf('3', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         ((m1_subset_1 @ (k4_relset_1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.07/1.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.07/1.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.26  thf('4', plain,
% 1.07/1.26      ((m1_subset_1 @ 
% 1.07/1.26        (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['0', '3'])).
% 1.07/1.26  thf('5', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('6', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(redefinition_k4_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.26     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.26       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.07/1.26  thf('7', plain,
% 1.07/1.26      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.07/1.26          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.07/1.26          | ((k4_relset_1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 1.07/1.26              = (k5_relat_1 @ X23 @ X26)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.07/1.26  thf('8', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.07/1.26            = (k5_relat_1 @ sk_D @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.07/1.26      inference('sup-', [status(thm)], ['6', '7'])).
% 1.07/1.26  thf('9', plain,
% 1.07/1.26      (((k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.07/1.26         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.07/1.26      inference('sup-', [status(thm)], ['5', '8'])).
% 1.07/1.26  thf('10', plain,
% 1.07/1.26      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.07/1.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.07/1.26      inference('demod', [status(thm)], ['4', '9'])).
% 1.07/1.26  thf(redefinition_k2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.07/1.26  thf('11', plain,
% 1.07/1.26      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.07/1.26         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.07/1.26          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.26  thf('12', plain,
% 1.07/1.26      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.07/1.26         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['10', '11'])).
% 1.07/1.26  thf('13', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(d1_funct_2, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.26           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.07/1.26             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.07/1.26         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.26           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.07/1.26             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.07/1.26  thf(zf_stmt_1, axiom,
% 1.07/1.26    (![C:$i,B:$i,A:$i]:
% 1.07/1.26     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.07/1.26       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.07/1.26  thf('14', plain,
% 1.07/1.26      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.07/1.26         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.07/1.26          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.07/1.26          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.07/1.26  thf('15', plain,
% 1.07/1.26      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.07/1.26        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['13', '14'])).
% 1.07/1.26  thf(zf_stmt_2, axiom,
% 1.07/1.26    (![B:$i,A:$i]:
% 1.07/1.26     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.26       ( zip_tseitin_0 @ B @ A ) ))).
% 1.07/1.26  thf('16', plain,
% 1.07/1.26      (![X29 : $i, X30 : $i]:
% 1.07/1.26         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.07/1.26  thf('17', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.07/1.26  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.07/1.26  thf(zf_stmt_5, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.07/1.26         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.26           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.07/1.26             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.07/1.26  thf('18', plain,
% 1.07/1.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.26         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.07/1.26          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.07/1.26          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.07/1.26  thf('19', plain,
% 1.07/1.26      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['17', '18'])).
% 1.07/1.26  thf('20', plain,
% 1.07/1.26      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['16', '19'])).
% 1.07/1.26  thf('21', plain, (((sk_C) != (k1_xboole_0))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('22', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.07/1.26      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 1.07/1.26  thf('23', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(redefinition_k1_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.07/1.26  thf('24', plain,
% 1.07/1.26      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.07/1.26         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 1.07/1.26          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.07/1.26  thf('25', plain,
% 1.07/1.26      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.07/1.26      inference('sup-', [status(thm)], ['23', '24'])).
% 1.07/1.26  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.07/1.26      inference('demod', [status(thm)], ['15', '22', '25'])).
% 1.07/1.26  thf('27', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('28', plain,
% 1.07/1.26      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.07/1.26         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.07/1.26          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.26  thf('29', plain,
% 1.07/1.26      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.07/1.26      inference('sup-', [status(thm)], ['27', '28'])).
% 1.07/1.26  thf('30', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.07/1.26      inference('sup+', [status(thm)], ['29', '30'])).
% 1.07/1.26  thf(t47_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ A ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( v1_relat_1 @ B ) =>
% 1.07/1.26           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 1.07/1.26             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.07/1.26  thf('32', plain,
% 1.07/1.26      (![X6 : $i, X7 : $i]:
% 1.07/1.26         (~ (v1_relat_1 @ X6)
% 1.07/1.26          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X7)) = (k2_relat_1 @ X7))
% 1.07/1.26          | ~ (r1_tarski @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X6))
% 1.07/1.26          | ~ (v1_relat_1 @ X7))),
% 1.07/1.26      inference('cnf', [status(esa)], [t47_relat_1])).
% 1.07/1.26  thf('33', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 1.07/1.26          | ~ (v1_relat_1 @ sk_D))),
% 1.07/1.26      inference('sup-', [status(thm)], ['31', '32'])).
% 1.07/1.26  thf('34', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc2_relat_1, axiom,
% 1.07/1.26    (![A:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ A ) =>
% 1.07/1.26       ( ![B:$i]:
% 1.07/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.07/1.26  thf('35', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.26          | (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.26  thf('36', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 1.07/1.26      inference('sup-', [status(thm)], ['34', '35'])).
% 1.07/1.26  thf(fc6_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.07/1.26  thf('37', plain,
% 1.07/1.26      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.26  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.07/1.26  thf('39', plain,
% 1.07/1.26      (![X0 : $i]:
% 1.07/1.26         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 1.07/1.26          | ~ (v1_relat_1 @ X0)
% 1.07/1.26          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 1.07/1.26      inference('demod', [status(thm)], ['33', '38'])).
% 1.07/1.26  thf('40', plain,
% 1.07/1.26      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.07/1.26        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (k2_relat_1 @ sk_E))
% 1.07/1.26        | ~ (v1_relat_1 @ sk_E))),
% 1.07/1.26      inference('sup-', [status(thm)], ['26', '39'])).
% 1.07/1.26  thf('41', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(cc2_relset_1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i]:
% 1.07/1.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.26       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.07/1.26  thf('42', plain,
% 1.07/1.26      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.07/1.26         ((v5_relat_1 @ X8 @ X10)
% 1.07/1.26          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.26  thf('43', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.07/1.26      inference('sup-', [status(thm)], ['41', '42'])).
% 1.07/1.26  thf(d19_relat_1, axiom,
% 1.07/1.26    (![A:$i,B:$i]:
% 1.07/1.26     ( ( v1_relat_1 @ B ) =>
% 1.07/1.26       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.07/1.26  thf('44', plain,
% 1.07/1.26      (![X2 : $i, X3 : $i]:
% 1.07/1.26         (~ (v5_relat_1 @ X2 @ X3)
% 1.07/1.26          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 1.07/1.26          | ~ (v1_relat_1 @ X2))),
% 1.07/1.26      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.07/1.26  thf('45', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.07/1.26      inference('sup-', [status(thm)], ['43', '44'])).
% 1.07/1.26  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.26      inference('demod', [status(thm)], ['36', '37'])).
% 1.07/1.26  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['45', '46'])).
% 1.07/1.26  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.07/1.26      inference('sup+', [status(thm)], ['29', '30'])).
% 1.07/1.26  thf('49', plain, ((r1_tarski @ sk_B @ sk_B)),
% 1.07/1.26      inference('demod', [status(thm)], ['47', '48'])).
% 1.07/1.26  thf('50', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('51', plain,
% 1.07/1.26      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.07/1.26         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.07/1.26          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.26  thf('52', plain,
% 1.07/1.26      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 1.07/1.26      inference('sup-', [status(thm)], ['50', '51'])).
% 1.07/1.26  thf('53', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('54', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.07/1.26      inference('sup+', [status(thm)], ['52', '53'])).
% 1.07/1.26  thf('55', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('56', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.07/1.26          | (v1_relat_1 @ X0)
% 1.07/1.26          | ~ (v1_relat_1 @ X1))),
% 1.07/1.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.07/1.26  thf('57', plain,
% 1.07/1.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 1.07/1.26      inference('sup-', [status(thm)], ['55', '56'])).
% 1.07/1.26  thf('58', plain,
% 1.07/1.26      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.07/1.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.07/1.26  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 1.07/1.26      inference('demod', [status(thm)], ['57', '58'])).
% 1.07/1.26  thf('60', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.07/1.26      inference('demod', [status(thm)], ['40', '49', '54', '59'])).
% 1.07/1.26  thf('61', plain,
% 1.07/1.26      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.07/1.26      inference('demod', [status(thm)], ['12', '60'])).
% 1.07/1.26  thf('62', plain,
% 1.07/1.26      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.07/1.26         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('63', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('64', plain,
% 1.07/1.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf(redefinition_k1_partfun1, axiom,
% 1.07/1.26    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.26     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.26         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.26         ( v1_funct_1 @ F ) & 
% 1.07/1.26         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.26       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.07/1.26  thf('65', plain,
% 1.07/1.26      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.07/1.26         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.07/1.26          | ~ (v1_funct_1 @ X37)
% 1.07/1.26          | ~ (v1_funct_1 @ X40)
% 1.07/1.26          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.07/1.26          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 1.07/1.26              = (k5_relat_1 @ X37 @ X40)))),
% 1.07/1.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.07/1.26  thf('66', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.07/1.26            = (k5_relat_1 @ sk_D @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0)
% 1.07/1.26          | ~ (v1_funct_1 @ sk_D))),
% 1.07/1.26      inference('sup-', [status(thm)], ['64', '65'])).
% 1.07/1.26  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('68', plain,
% 1.07/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.26         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.07/1.26            = (k5_relat_1 @ sk_D @ X0))
% 1.07/1.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.07/1.26          | ~ (v1_funct_1 @ X0))),
% 1.07/1.26      inference('demod', [status(thm)], ['66', '67'])).
% 1.07/1.26  thf('69', plain,
% 1.07/1.26      ((~ (v1_funct_1 @ sk_E)
% 1.07/1.26        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.07/1.26            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.07/1.26      inference('sup-', [status(thm)], ['63', '68'])).
% 1.07/1.26  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 1.07/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.26  thf('71', plain,
% 1.07/1.26      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.07/1.26         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.07/1.26      inference('demod', [status(thm)], ['69', '70'])).
% 1.07/1.26  thf('72', plain,
% 1.07/1.26      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 1.07/1.26      inference('demod', [status(thm)], ['62', '71'])).
% 1.07/1.26  thf('73', plain, ($false),
% 1.07/1.26      inference('simplify_reflect-', [status(thm)], ['61', '72'])).
% 1.07/1.26  
% 1.07/1.26  % SZS output end Refutation
% 1.07/1.26  
% 1.07/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

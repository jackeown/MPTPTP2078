%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UssFYm5XKc

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:42 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 160 expanded)
%              Number of leaves         :   36 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  890 (3295 expanded)
%              Number of equality atoms :   58 ( 241 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','7','16'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X11 @ X9 )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['22','29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X8 ) @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['40','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['33','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k2_relset_1 @ X13 @ X14 @ X12 )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('59',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['47','49','54','59'])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['19','60'])).

thf('62',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('64',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UssFYm5XKc
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.97/1.16  % Solved by: fo/fo7.sh
% 0.97/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.16  % done 534 iterations in 0.730s
% 0.97/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.97/1.16  % SZS output start Refutation
% 0.97/1.16  thf(sk_C_type, type, sk_C: $i).
% 0.97/1.16  thf(sk_D_type, type, sk_D: $i).
% 0.97/1.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.97/1.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.97/1.16  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.97/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.97/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.97/1.16  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.97/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.97/1.16  thf(sk_E_type, type, sk_E: $i).
% 0.97/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.97/1.16  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.97/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.97/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.97/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.97/1.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.97/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.97/1.16  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.97/1.16  thf(t20_funct_2, conjecture,
% 0.97/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.16     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.97/1.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.97/1.16       ( ![E:$i]:
% 0.97/1.16         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.97/1.16             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.97/1.16           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.97/1.16               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.97/1.16             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.97/1.16               ( ( k2_relset_1 @
% 0.97/1.16                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.97/1.16                 ( C ) ) ) ) ) ) ))).
% 0.97/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.16    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.97/1.16        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.97/1.16            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.97/1.16          ( ![E:$i]:
% 0.97/1.16            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.97/1.16                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.97/1.16              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.97/1.16                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.97/1.16                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.97/1.16                  ( ( k2_relset_1 @
% 0.97/1.16                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.97/1.16                    ( C ) ) ) ) ) ) ) )),
% 0.97/1.16    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 0.97/1.16  thf('0', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('1', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(dt_k1_partfun1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.97/1.16     ( ( ( v1_funct_1 @ E ) & 
% 0.97/1.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.97/1.16         ( v1_funct_1 @ F ) & 
% 0.97/1.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.97/1.16       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.97/1.16         ( m1_subset_1 @
% 0.97/1.16           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.97/1.16           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.97/1.16  thf('2', plain,
% 0.97/1.16      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.97/1.16         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.97/1.16          | ~ (v1_funct_1 @ X23)
% 0.97/1.16          | ~ (v1_funct_1 @ X26)
% 0.97/1.16          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.97/1.16          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.97/1.16             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.97/1.16      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.97/1.16  thf('3', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.97/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.97/1.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.97/1.16          | ~ (v1_funct_1 @ X1)
% 0.97/1.16          | ~ (v1_funct_1 @ sk_D))),
% 0.97/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.97/1.16  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('5', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.97/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.97/1.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.97/1.16          | ~ (v1_funct_1 @ X1))),
% 0.97/1.16      inference('demod', [status(thm)], ['3', '4'])).
% 0.97/1.16  thf('6', plain,
% 0.97/1.16      ((~ (v1_funct_1 @ sk_E)
% 0.97/1.16        | (m1_subset_1 @ 
% 0.97/1.16           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.97/1.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.97/1.16      inference('sup-', [status(thm)], ['0', '5'])).
% 0.97/1.16  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('8', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('9', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(redefinition_k1_partfun1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.97/1.16     ( ( ( v1_funct_1 @ E ) & 
% 0.97/1.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.97/1.16         ( v1_funct_1 @ F ) & 
% 0.97/1.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.97/1.16       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.97/1.16  thf('10', plain,
% 0.97/1.16      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.97/1.16         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.97/1.16          | ~ (v1_funct_1 @ X29)
% 0.97/1.16          | ~ (v1_funct_1 @ X32)
% 0.97/1.16          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.97/1.16          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.97/1.16              = (k5_relat_1 @ X29 @ X32)))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.97/1.16  thf('11', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.97/1.16            = (k5_relat_1 @ sk_D @ X0))
% 0.97/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.97/1.16          | ~ (v1_funct_1 @ X0)
% 0.97/1.16          | ~ (v1_funct_1 @ sk_D))),
% 0.97/1.16      inference('sup-', [status(thm)], ['9', '10'])).
% 0.97/1.16  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('13', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.97/1.16            = (k5_relat_1 @ sk_D @ X0))
% 0.97/1.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.97/1.16          | ~ (v1_funct_1 @ X0))),
% 0.97/1.16      inference('demod', [status(thm)], ['11', '12'])).
% 0.97/1.16  thf('14', plain,
% 0.97/1.16      ((~ (v1_funct_1 @ sk_E)
% 0.97/1.16        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.97/1.16            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['8', '13'])).
% 0.97/1.16  thf('15', plain, ((v1_funct_1 @ sk_E)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('16', plain,
% 0.97/1.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.97/1.16         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.97/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.97/1.16  thf('17', plain,
% 0.97/1.16      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 0.97/1.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.97/1.16      inference('demod', [status(thm)], ['6', '7', '16'])).
% 0.97/1.16  thf(redefinition_k2_relset_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.16       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.97/1.16  thf('18', plain,
% 0.97/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.97/1.16         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.97/1.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.97/1.16  thf('19', plain,
% 0.97/1.16      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 0.97/1.16         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['17', '18'])).
% 0.97/1.16  thf('20', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(d1_funct_2, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.16       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.97/1.16           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.97/1.16             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.97/1.16         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.97/1.16           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.97/1.16             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.97/1.16  thf(zf_stmt_1, axiom,
% 0.97/1.16    (![C:$i,B:$i,A:$i]:
% 0.97/1.16     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.97/1.16       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.97/1.16  thf('21', plain,
% 0.97/1.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.97/1.16         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.97/1.16          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.97/1.16          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.97/1.16  thf('22', plain,
% 0.97/1.16      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 0.97/1.16        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 0.97/1.16      inference('sup-', [status(thm)], ['20', '21'])).
% 0.97/1.16  thf(zf_stmt_2, axiom,
% 0.97/1.16    (![B:$i,A:$i]:
% 0.97/1.16     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.97/1.16       ( zip_tseitin_0 @ B @ A ) ))).
% 0.97/1.16  thf('23', plain,
% 0.97/1.16      (![X15 : $i, X16 : $i]:
% 0.97/1.16         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.97/1.16  thf('24', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.97/1.16  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.97/1.16  thf(zf_stmt_5, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.16       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.97/1.16         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.97/1.16           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.97/1.16             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.97/1.16  thf('25', plain,
% 0.97/1.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.97/1.16         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.97/1.16          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.97/1.16          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.97/1.16  thf('26', plain,
% 0.97/1.16      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.97/1.16      inference('sup-', [status(thm)], ['24', '25'])).
% 0.97/1.16  thf('27', plain,
% 0.97/1.16      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 0.97/1.16      inference('sup-', [status(thm)], ['23', '26'])).
% 0.97/1.16  thf('28', plain, (((sk_C) != (k1_xboole_0))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('29', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 0.97/1.16      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.97/1.16  thf('30', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(redefinition_k1_relset_1, axiom,
% 0.97/1.16    (![A:$i,B:$i,C:$i]:
% 0.97/1.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.97/1.16       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.97/1.16  thf('31', plain,
% 0.97/1.16      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.97/1.16         (((k1_relset_1 @ X10 @ X11 @ X9) = (k1_relat_1 @ X9))
% 0.97/1.16          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.97/1.16  thf('32', plain,
% 0.97/1.16      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.97/1.16      inference('sup-', [status(thm)], ['30', '31'])).
% 0.97/1.16  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 0.97/1.16      inference('demod', [status(thm)], ['22', '29', '32'])).
% 0.97/1.16  thf('34', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('35', plain,
% 0.97/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.97/1.16         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.97/1.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.97/1.16  thf('36', plain,
% 0.97/1.16      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.97/1.16      inference('sup-', [status(thm)], ['34', '35'])).
% 0.97/1.16  thf('37', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 0.97/1.16      inference('sup+', [status(thm)], ['36', '37'])).
% 0.97/1.16  thf(t47_relat_1, axiom,
% 0.97/1.16    (![A:$i]:
% 0.97/1.16     ( ( v1_relat_1 @ A ) =>
% 0.97/1.16       ( ![B:$i]:
% 0.97/1.16         ( ( v1_relat_1 @ B ) =>
% 0.97/1.16           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.97/1.16             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.97/1.16  thf('39', plain,
% 0.97/1.16      (![X7 : $i, X8 : $i]:
% 0.97/1.16         (~ (v1_relat_1 @ X7)
% 0.97/1.16          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X8)) = (k2_relat_1 @ X8))
% 0.97/1.16          | ~ (r1_tarski @ (k1_relat_1 @ X8) @ (k2_relat_1 @ X7))
% 0.97/1.16          | ~ (v1_relat_1 @ X8))),
% 0.97/1.16      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.97/1.16  thf('40', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 0.97/1.16          | ~ (v1_relat_1 @ X0)
% 0.97/1.16          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0))
% 0.97/1.16          | ~ (v1_relat_1 @ sk_D))),
% 0.97/1.16      inference('sup-', [status(thm)], ['38', '39'])).
% 0.97/1.16  thf('41', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf(cc2_relat_1, axiom,
% 0.97/1.16    (![A:$i]:
% 0.97/1.16     ( ( v1_relat_1 @ A ) =>
% 0.97/1.16       ( ![B:$i]:
% 0.97/1.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.97/1.16  thf('42', plain,
% 0.97/1.16      (![X3 : $i, X4 : $i]:
% 0.97/1.16         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.97/1.16          | (v1_relat_1 @ X3)
% 0.97/1.16          | ~ (v1_relat_1 @ X4))),
% 0.97/1.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.97/1.16  thf('43', plain,
% 0.97/1.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.97/1.16      inference('sup-', [status(thm)], ['41', '42'])).
% 0.97/1.16  thf(fc6_relat_1, axiom,
% 0.97/1.16    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.97/1.16  thf('44', plain,
% 0.97/1.16      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.97/1.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.97/1.16  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.97/1.16      inference('demod', [status(thm)], ['43', '44'])).
% 0.97/1.16  thf('46', plain,
% 0.97/1.16      (![X0 : $i]:
% 0.97/1.16         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 0.97/1.16          | ~ (v1_relat_1 @ X0)
% 0.97/1.16          | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k2_relat_1 @ X0)))),
% 0.97/1.16      inference('demod', [status(thm)], ['40', '45'])).
% 0.97/1.16  thf('47', plain,
% 0.97/1.16      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.97/1.16        | ((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (k2_relat_1 @ sk_E))
% 0.97/1.16        | ~ (v1_relat_1 @ sk_E))),
% 0.97/1.16      inference('sup-', [status(thm)], ['33', '46'])).
% 0.97/1.16  thf(d10_xboole_0, axiom,
% 0.97/1.16    (![A:$i,B:$i]:
% 0.97/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.16  thf('48', plain,
% 0.97/1.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.97/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.16  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.97/1.16      inference('simplify', [status(thm)], ['48'])).
% 0.97/1.16  thf('50', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('51', plain,
% 0.97/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.97/1.16         (((k2_relset_1 @ X13 @ X14 @ X12) = (k2_relat_1 @ X12))
% 0.97/1.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.97/1.16      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.97/1.16  thf('52', plain,
% 0.97/1.16      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 0.97/1.16      inference('sup-', [status(thm)], ['50', '51'])).
% 0.97/1.16  thf('53', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('54', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 0.97/1.16      inference('sup+', [status(thm)], ['52', '53'])).
% 0.97/1.16  thf('55', plain,
% 0.97/1.16      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('56', plain,
% 0.97/1.16      (![X3 : $i, X4 : $i]:
% 0.97/1.16         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.97/1.16          | (v1_relat_1 @ X3)
% 0.97/1.16          | ~ (v1_relat_1 @ X4))),
% 0.97/1.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.97/1.16  thf('57', plain,
% 0.97/1.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.97/1.16      inference('sup-', [status(thm)], ['55', '56'])).
% 0.97/1.16  thf('58', plain,
% 0.97/1.16      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.97/1.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.97/1.16  thf('59', plain, ((v1_relat_1 @ sk_E)),
% 0.97/1.16      inference('demod', [status(thm)], ['57', '58'])).
% 0.97/1.16  thf('60', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.97/1.16      inference('demod', [status(thm)], ['47', '49', '54', '59'])).
% 0.97/1.16  thf('61', plain,
% 0.97/1.16      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 0.97/1.16      inference('demod', [status(thm)], ['19', '60'])).
% 0.97/1.16  thf('62', plain,
% 0.97/1.16      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.97/1.16         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 0.97/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.16  thf('63', plain,
% 0.97/1.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.97/1.16         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.97/1.16      inference('demod', [status(thm)], ['14', '15'])).
% 0.97/1.16  thf('64', plain,
% 0.97/1.16      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 0.97/1.16      inference('demod', [status(thm)], ['62', '63'])).
% 0.97/1.16  thf('65', plain, ($false),
% 0.97/1.16      inference('simplify_reflect-', [status(thm)], ['61', '64'])).
% 0.97/1.16  
% 0.97/1.16  % SZS output end Refutation
% 0.97/1.16  
% 0.97/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

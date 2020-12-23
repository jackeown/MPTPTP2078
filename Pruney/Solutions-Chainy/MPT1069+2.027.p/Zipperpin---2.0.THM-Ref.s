%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SWLI0PU3uK

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:04 EST 2020

% Result     : Theorem 7.06s
% Output     : Refutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 373 expanded)
%              Number of leaves         :   47 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          : 1296 (7631 expanded)
%              Number of equality atoms :   78 ( 347 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
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

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13','14','31'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['54','55'])).

thf('57',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['48','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['10','13','14','31'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('59',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ X38 )
      | ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X40 @ X37 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('62',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( v1_funct_2 @ X35 @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('63',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['21','30'])).

thf('67',plain,(
    v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','67','68'])).

thf('70',plain,
    ( ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['57','69'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ( ( k7_partfun1 @ X28 @ X27 @ X26 )
        = ( k1_funct_1 @ X27 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v5_relat_1 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('75',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['72','75','76'])).

thf('78',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','77'])).

thf('79',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ X30 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X30 @ X31 @ X34 @ X29 @ X33 ) @ X32 )
        = ( k1_funct_1 @ X33 @ ( k1_funct_1 @ X29 @ X32 ) ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X30 @ X31 @ X29 ) @ ( k1_relset_1 @ X31 @ X34 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('86',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','90'])).

thf('92',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('93',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['80','97'])).

thf('99',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['79','98'])).

thf('100',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_E )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['42','101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SWLI0PU3uK
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:36:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 7.06/7.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.06/7.23  % Solved by: fo/fo7.sh
% 7.06/7.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.06/7.23  % done 6519 iterations in 6.766s
% 7.06/7.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.06/7.23  % SZS output start Refutation
% 7.06/7.23  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.06/7.23  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.06/7.23  thf(sk_B_type, type, sk_B: $i).
% 7.06/7.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.06/7.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.06/7.23  thf(sk_E_type, type, sk_E: $i).
% 7.06/7.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.06/7.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.06/7.23  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 7.06/7.23  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.06/7.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.06/7.23  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.06/7.23  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 7.06/7.23  thf(sk_C_type, type, sk_C: $i).
% 7.06/7.23  thf(sk_D_type, type, sk_D: $i).
% 7.06/7.23  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.06/7.23  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.06/7.23  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.06/7.23  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.06/7.23  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.06/7.23  thf(sk_F_type, type, sk_F: $i).
% 7.06/7.23  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.06/7.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.06/7.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.06/7.23  thf(sk_A_type, type, sk_A: $i).
% 7.06/7.23  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.06/7.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.06/7.23  thf(t186_funct_2, conjecture,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.06/7.23       ( ![D:$i]:
% 7.06/7.23         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.06/7.23             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.06/7.23           ( ![E:$i]:
% 7.06/7.23             ( ( ( v1_funct_1 @ E ) & 
% 7.06/7.23                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 7.06/7.23               ( ![F:$i]:
% 7.06/7.23                 ( ( m1_subset_1 @ F @ B ) =>
% 7.06/7.23                   ( ( r1_tarski @
% 7.06/7.23                       ( k2_relset_1 @ B @ C @ D ) @ 
% 7.06/7.23                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 7.06/7.23                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.06/7.23                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 7.06/7.23                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.06/7.23  thf(zf_stmt_0, negated_conjecture,
% 7.06/7.23    (~( ![A:$i,B:$i,C:$i]:
% 7.06/7.23        ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.06/7.23          ( ![D:$i]:
% 7.06/7.23            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.06/7.23                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.06/7.23              ( ![E:$i]:
% 7.06/7.23                ( ( ( v1_funct_1 @ E ) & 
% 7.06/7.23                    ( m1_subset_1 @
% 7.06/7.23                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 7.06/7.23                  ( ![F:$i]:
% 7.06/7.23                    ( ( m1_subset_1 @ F @ B ) =>
% 7.06/7.23                      ( ( r1_tarski @
% 7.06/7.23                          ( k2_relset_1 @ B @ C @ D ) @ 
% 7.06/7.23                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 7.06/7.23                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.06/7.23                          ( ( k1_funct_1 @
% 7.06/7.23                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 7.06/7.23                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 7.06/7.23    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 7.06/7.23  thf('0', plain,
% 7.06/7.23      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 7.06/7.23        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('1', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(redefinition_k1_relset_1, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.06/7.23       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.06/7.23  thf('2', plain,
% 7.06/7.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.06/7.23         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 7.06/7.23          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 7.06/7.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.06/7.23  thf('3', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('sup-', [status(thm)], ['1', '2'])).
% 7.06/7.23  thf('4', plain,
% 7.06/7.23      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('demod', [status(thm)], ['0', '3'])).
% 7.06/7.23  thf('5', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(redefinition_k2_relset_1, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.06/7.23       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.06/7.23  thf('6', plain,
% 7.06/7.23      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.06/7.23         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 7.06/7.23          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 7.06/7.23      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.06/7.23  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 7.06/7.23      inference('sup-', [status(thm)], ['5', '6'])).
% 7.06/7.23  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('demod', [status(thm)], ['4', '7'])).
% 7.06/7.23  thf(t4_funct_2, axiom,
% 7.06/7.23    (![A:$i,B:$i]:
% 7.06/7.23     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 7.06/7.23       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 7.06/7.23         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 7.06/7.23           ( m1_subset_1 @
% 7.06/7.23             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 7.06/7.23  thf('9', plain,
% 7.06/7.23      (![X35 : $i, X36 : $i]:
% 7.06/7.23         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 7.06/7.23          | (m1_subset_1 @ X35 @ 
% 7.06/7.23             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ X36)))
% 7.06/7.23          | ~ (v1_funct_1 @ X35)
% 7.06/7.23          | ~ (v1_relat_1 @ X35))),
% 7.06/7.23      inference('cnf', [status(esa)], [t4_funct_2])).
% 7.06/7.23  thf('10', plain,
% 7.06/7.23      ((~ (v1_relat_1 @ sk_D)
% 7.06/7.23        | ~ (v1_funct_1 @ sk_D)
% 7.06/7.23        | (m1_subset_1 @ sk_D @ 
% 7.06/7.23           (k1_zfmisc_1 @ 
% 7.06/7.23            (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E)))))),
% 7.06/7.23      inference('sup-', [status(thm)], ['8', '9'])).
% 7.06/7.23  thf('11', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(cc1_relset_1, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.06/7.23       ( v1_relat_1 @ C ) ))).
% 7.06/7.23  thf('12', plain,
% 7.06/7.23      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.06/7.23         ((v1_relat_1 @ X3)
% 7.06/7.23          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 7.06/7.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.06/7.23  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 7.06/7.23      inference('sup-', [status(thm)], ['11', '12'])).
% 7.06/7.23  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('15', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(d1_funct_2, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.06/7.23       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.06/7.23           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.06/7.23             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.06/7.23         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.06/7.23           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.06/7.23             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.06/7.23  thf(zf_stmt_1, axiom,
% 7.06/7.23    (![C:$i,B:$i,A:$i]:
% 7.06/7.23     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.06/7.23       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.06/7.23  thf('16', plain,
% 7.06/7.23      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.06/7.23         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 7.06/7.23          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 7.06/7.23          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.06/7.23  thf('17', plain,
% 7.06/7.23      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 7.06/7.23        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 7.06/7.23      inference('sup-', [status(thm)], ['15', '16'])).
% 7.06/7.23  thf('18', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('19', plain,
% 7.06/7.23      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.06/7.23         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 7.06/7.23          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 7.06/7.23      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.06/7.23  thf('20', plain,
% 7.06/7.23      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 7.06/7.23      inference('sup-', [status(thm)], ['18', '19'])).
% 7.06/7.23  thf('21', plain,
% 7.06/7.23      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 7.06/7.23      inference('demod', [status(thm)], ['17', '20'])).
% 7.06/7.23  thf('22', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.06/7.23  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 7.06/7.23  thf(zf_stmt_4, axiom,
% 7.06/7.23    (![B:$i,A:$i]:
% 7.06/7.23     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.06/7.23       ( zip_tseitin_0 @ B @ A ) ))).
% 7.06/7.23  thf(zf_stmt_5, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.06/7.23       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.06/7.23         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.06/7.23           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.06/7.23             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.06/7.23  thf('23', plain,
% 7.06/7.23      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.06/7.23         (~ (zip_tseitin_0 @ X23 @ X24)
% 7.06/7.23          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 7.06/7.23          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.06/7.23  thf('24', plain,
% 7.06/7.23      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 7.06/7.23      inference('sup-', [status(thm)], ['22', '23'])).
% 7.06/7.23  thf('25', plain,
% 7.06/7.23      (![X18 : $i, X19 : $i]:
% 7.06/7.23         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_4])).
% 7.06/7.23  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 7.06/7.23  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.06/7.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.06/7.23  thf('27', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 7.06/7.23      inference('sup+', [status(thm)], ['25', '26'])).
% 7.06/7.23  thf('28', plain, (~ (v1_xboole_0 @ sk_C)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('29', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 7.06/7.23      inference('sup-', [status(thm)], ['27', '28'])).
% 7.06/7.23  thf('30', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 7.06/7.23      inference('demod', [status(thm)], ['24', '29'])).
% 7.06/7.23  thf('31', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 7.06/7.23      inference('demod', [status(thm)], ['21', '30'])).
% 7.06/7.23  thf('32', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_D @ 
% 7.06/7.23        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E))))),
% 7.06/7.23      inference('demod', [status(thm)], ['10', '13', '14', '31'])).
% 7.06/7.23  thf(cc4_relset_1, axiom,
% 7.06/7.23    (![A:$i,B:$i]:
% 7.06/7.23     ( ( v1_xboole_0 @ A ) =>
% 7.06/7.23       ( ![C:$i]:
% 7.06/7.23         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 7.06/7.23           ( v1_xboole_0 @ C ) ) ) ))).
% 7.06/7.23  thf('33', plain,
% 7.06/7.23      (![X9 : $i, X10 : $i, X11 : $i]:
% 7.06/7.23         (~ (v1_xboole_0 @ X9)
% 7.06/7.23          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 7.06/7.23          | (v1_xboole_0 @ X10))),
% 7.06/7.23      inference('cnf', [status(esa)], [cc4_relset_1])).
% 7.06/7.23  thf('34', plain,
% 7.06/7.23      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_E)))),
% 7.06/7.23      inference('sup-', [status(thm)], ['32', '33'])).
% 7.06/7.23  thf(l13_xboole_0, axiom,
% 7.06/7.23    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 7.06/7.23  thf('35', plain,
% 7.06/7.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.06/7.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.06/7.23  thf(t60_relat_1, axiom,
% 7.06/7.23    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 7.06/7.23     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 7.06/7.23  thf('36', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 7.06/7.23      inference('cnf', [status(esa)], [t60_relat_1])).
% 7.06/7.23  thf('37', plain,
% 7.06/7.23      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.06/7.23      inference('sup+', [status(thm)], ['35', '36'])).
% 7.06/7.23  thf('38', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 7.06/7.23      inference('demod', [status(thm)], ['21', '30'])).
% 7.06/7.23  thf('39', plain, ((((sk_B) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_D))),
% 7.06/7.23      inference('sup+', [status(thm)], ['37', '38'])).
% 7.06/7.23  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('41', plain, (~ (v1_xboole_0 @ sk_D)),
% 7.06/7.23      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 7.06/7.23  thf('42', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('clc', [status(thm)], ['34', '41'])).
% 7.06/7.23  thf('43', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(cc2_relset_1, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.06/7.23       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.06/7.23  thf('44', plain,
% 7.06/7.23      (![X6 : $i, X7 : $i, X8 : $i]:
% 7.06/7.23         ((v5_relat_1 @ X6 @ X8)
% 7.06/7.23          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 7.06/7.23      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.06/7.23  thf('45', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 7.06/7.23      inference('sup-', [status(thm)], ['43', '44'])).
% 7.06/7.23  thf('46', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(t2_subset, axiom,
% 7.06/7.23    (![A:$i,B:$i]:
% 7.06/7.23     ( ( m1_subset_1 @ A @ B ) =>
% 7.06/7.23       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 7.06/7.23  thf('47', plain,
% 7.06/7.23      (![X1 : $i, X2 : $i]:
% 7.06/7.23         ((r2_hidden @ X1 @ X2)
% 7.06/7.23          | (v1_xboole_0 @ X2)
% 7.06/7.23          | ~ (m1_subset_1 @ X1 @ X2))),
% 7.06/7.23      inference('cnf', [status(esa)], [t2_subset])).
% 7.06/7.23  thf('48', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 7.06/7.23      inference('sup-', [status(thm)], ['46', '47'])).
% 7.06/7.23  thf('49', plain,
% 7.06/7.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.06/7.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.06/7.23  thf('50', plain,
% 7.06/7.23      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.06/7.23      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.06/7.23  thf('51', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i]:
% 7.06/7.23         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 7.06/7.23      inference('sup+', [status(thm)], ['49', '50'])).
% 7.06/7.23  thf('52', plain, (((sk_B) != (k1_xboole_0))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('53', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         (((X0) != (k1_xboole_0))
% 7.06/7.23          | ~ (v1_xboole_0 @ X0)
% 7.06/7.23          | ~ (v1_xboole_0 @ sk_B))),
% 7.06/7.23      inference('sup-', [status(thm)], ['51', '52'])).
% 7.06/7.23  thf('54', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 7.06/7.23      inference('simplify', [status(thm)], ['53'])).
% 7.06/7.23  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.06/7.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.06/7.23  thf('56', plain, (~ (v1_xboole_0 @ sk_B)),
% 7.06/7.23      inference('simplify_reflect+', [status(thm)], ['54', '55'])).
% 7.06/7.23  thf('57', plain, ((r2_hidden @ sk_F @ sk_B)),
% 7.06/7.23      inference('clc', [status(thm)], ['48', '56'])).
% 7.06/7.23  thf('58', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_D @ 
% 7.06/7.23        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E))))),
% 7.06/7.23      inference('demod', [status(thm)], ['10', '13', '14', '31'])).
% 7.06/7.23  thf(t7_funct_2, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i,D:$i]:
% 7.06/7.23     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 7.06/7.23         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.06/7.23       ( ( r2_hidden @ C @ A ) =>
% 7.06/7.23         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.06/7.23           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 7.06/7.23  thf('59', plain,
% 7.06/7.23      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 7.06/7.23         (~ (r2_hidden @ X37 @ X38)
% 7.06/7.23          | ((X39) = (k1_xboole_0))
% 7.06/7.23          | ~ (v1_funct_1 @ X40)
% 7.06/7.23          | ~ (v1_funct_2 @ X40 @ X38 @ X39)
% 7.06/7.23          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 7.06/7.23          | (r2_hidden @ (k1_funct_1 @ X40 @ X37) @ X39))),
% 7.06/7.23      inference('cnf', [status(esa)], [t7_funct_2])).
% 7.06/7.23  thf('60', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 7.06/7.23          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 7.06/7.23          | ~ (v1_funct_1 @ sk_D)
% 7.06/7.23          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 7.06/7.23          | ~ (r2_hidden @ X0 @ sk_B))),
% 7.06/7.23      inference('sup-', [status(thm)], ['58', '59'])).
% 7.06/7.23  thf('61', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('demod', [status(thm)], ['4', '7'])).
% 7.06/7.23  thf('62', plain,
% 7.06/7.23      (![X35 : $i, X36 : $i]:
% 7.06/7.23         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 7.06/7.23          | (v1_funct_2 @ X35 @ (k1_relat_1 @ X35) @ X36)
% 7.06/7.23          | ~ (v1_funct_1 @ X35)
% 7.06/7.23          | ~ (v1_relat_1 @ X35))),
% 7.06/7.23      inference('cnf', [status(esa)], [t4_funct_2])).
% 7.06/7.23  thf('63', plain,
% 7.06/7.23      ((~ (v1_relat_1 @ sk_D)
% 7.06/7.23        | ~ (v1_funct_1 @ sk_D)
% 7.06/7.23        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E)))),
% 7.06/7.23      inference('sup-', [status(thm)], ['61', '62'])).
% 7.06/7.23  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 7.06/7.23      inference('sup-', [status(thm)], ['11', '12'])).
% 7.06/7.23  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('66', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 7.06/7.23      inference('demod', [status(thm)], ['21', '30'])).
% 7.06/7.23  thf('67', plain, ((v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 7.06/7.23  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('69', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 7.06/7.23          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 7.06/7.23          | ~ (r2_hidden @ X0 @ sk_B))),
% 7.06/7.23      inference('demod', [status(thm)], ['60', '67', '68'])).
% 7.06/7.23  thf('70', plain,
% 7.06/7.23      ((((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 7.06/7.23        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 7.06/7.23      inference('sup-', [status(thm)], ['57', '69'])).
% 7.06/7.23  thf(d8_partfun1, axiom,
% 7.06/7.23    (![A:$i,B:$i]:
% 7.06/7.23     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 7.06/7.23       ( ![C:$i]:
% 7.06/7.23         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 7.06/7.23           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 7.06/7.23  thf('71', plain,
% 7.06/7.23      (![X26 : $i, X27 : $i, X28 : $i]:
% 7.06/7.23         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 7.06/7.23          | ((k7_partfun1 @ X28 @ X27 @ X26) = (k1_funct_1 @ X27 @ X26))
% 7.06/7.23          | ~ (v1_funct_1 @ X27)
% 7.06/7.23          | ~ (v5_relat_1 @ X27 @ X28)
% 7.06/7.23          | ~ (v1_relat_1 @ X27))),
% 7.06/7.23      inference('cnf', [status(esa)], [d8_partfun1])).
% 7.06/7.23  thf('72', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 7.06/7.23          | ~ (v1_relat_1 @ sk_E)
% 7.06/7.23          | ~ (v5_relat_1 @ sk_E @ X0)
% 7.06/7.23          | ~ (v1_funct_1 @ sk_E)
% 7.06/7.23          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.06/7.23              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 7.06/7.23      inference('sup-', [status(thm)], ['70', '71'])).
% 7.06/7.23  thf('73', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('74', plain,
% 7.06/7.23      (![X3 : $i, X4 : $i, X5 : $i]:
% 7.06/7.23         ((v1_relat_1 @ X3)
% 7.06/7.23          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 7.06/7.23      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.06/7.23  thf('75', plain, ((v1_relat_1 @ sk_E)),
% 7.06/7.23      inference('sup-', [status(thm)], ['73', '74'])).
% 7.06/7.23  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('77', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 7.06/7.23          | ~ (v5_relat_1 @ sk_E @ X0)
% 7.06/7.23          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.06/7.23              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 7.06/7.23      inference('demod', [status(thm)], ['72', '75', '76'])).
% 7.06/7.23  thf('78', plain,
% 7.06/7.23      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.06/7.23          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 7.06/7.23        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 7.06/7.23      inference('sup-', [status(thm)], ['45', '77'])).
% 7.06/7.23  thf('79', plain,
% 7.06/7.23      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 7.06/7.23         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('80', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('81', plain,
% 7.06/7.23      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('sup-', [status(thm)], ['1', '2'])).
% 7.06/7.23  thf('82', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf(t185_funct_2, axiom,
% 7.06/7.23    (![A:$i,B:$i,C:$i]:
% 7.06/7.23     ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.06/7.23       ( ![D:$i]:
% 7.06/7.23         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.06/7.23             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.06/7.23           ( ![E:$i]:
% 7.06/7.23             ( ( ( v1_funct_1 @ E ) & 
% 7.06/7.23                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 7.06/7.23               ( ![F:$i]:
% 7.06/7.23                 ( ( m1_subset_1 @ F @ B ) =>
% 7.06/7.23                   ( ( r1_tarski @
% 7.06/7.23                       ( k2_relset_1 @ B @ C @ D ) @ 
% 7.06/7.23                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 7.06/7.23                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.06/7.23                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 7.06/7.23                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.06/7.23  thf('83', plain,
% 7.06/7.23      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 7.06/7.23         (~ (v1_funct_1 @ X29)
% 7.06/7.23          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 7.06/7.23          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 7.06/7.23          | ~ (m1_subset_1 @ X32 @ X30)
% 7.06/7.23          | ((k1_funct_1 @ (k8_funct_2 @ X30 @ X31 @ X34 @ X29 @ X33) @ X32)
% 7.06/7.23              = (k1_funct_1 @ X33 @ (k1_funct_1 @ X29 @ X32)))
% 7.06/7.23          | ((X30) = (k1_xboole_0))
% 7.06/7.23          | ~ (r1_tarski @ (k2_relset_1 @ X30 @ X31 @ X29) @ 
% 7.06/7.23               (k1_relset_1 @ X31 @ X34 @ X33))
% 7.06/7.23          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X34)))
% 7.06/7.23          | ~ (v1_funct_1 @ X33)
% 7.06/7.23          | (v1_xboole_0 @ X31))),
% 7.06/7.23      inference('cnf', [status(esa)], [t185_funct_2])).
% 7.06/7.23  thf('84', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         ((v1_xboole_0 @ sk_C)
% 7.06/7.23          | ~ (v1_funct_1 @ X0)
% 7.06/7.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 7.06/7.23          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 7.06/7.23               (k1_relset_1 @ sk_C @ X1 @ X0))
% 7.06/7.23          | ((sk_B) = (k1_xboole_0))
% 7.06/7.23          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 7.06/7.23              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.06/7.23          | ~ (m1_subset_1 @ X2 @ sk_B)
% 7.06/7.23          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 7.06/7.23          | ~ (v1_funct_1 @ sk_D))),
% 7.06/7.23      inference('sup-', [status(thm)], ['82', '83'])).
% 7.06/7.23  thf('85', plain,
% 7.06/7.23      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 7.06/7.23      inference('sup-', [status(thm)], ['5', '6'])).
% 7.06/7.23  thf('86', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('87', plain, ((v1_funct_1 @ sk_D)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('88', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         ((v1_xboole_0 @ sk_C)
% 7.06/7.23          | ~ (v1_funct_1 @ X0)
% 7.06/7.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 7.06/7.23          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 7.06/7.23          | ((sk_B) = (k1_xboole_0))
% 7.06/7.23          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 7.06/7.23              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.06/7.23          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 7.06/7.23      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 7.06/7.23  thf('89', plain, (((sk_B) != (k1_xboole_0))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('90', plain,
% 7.06/7.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.06/7.23         ((v1_xboole_0 @ sk_C)
% 7.06/7.23          | ~ (v1_funct_1 @ X0)
% 7.06/7.23          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 7.06/7.23          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 7.06/7.23          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 7.06/7.23              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.06/7.23          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 7.06/7.23      inference('simplify_reflect-', [status(thm)], ['88', '89'])).
% 7.06/7.23  thf('91', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 7.06/7.23          | ~ (m1_subset_1 @ X0 @ sk_B)
% 7.06/7.23          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 7.06/7.23              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.06/7.23          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 7.06/7.23          | ~ (v1_funct_1 @ sk_E)
% 7.06/7.23          | (v1_xboole_0 @ sk_C))),
% 7.06/7.23      inference('sup-', [status(thm)], ['81', '90'])).
% 7.06/7.23  thf('92', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 7.06/7.23      inference('demod', [status(thm)], ['4', '7'])).
% 7.06/7.23  thf('93', plain,
% 7.06/7.23      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('94', plain, ((v1_funct_1 @ sk_E)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('95', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         (~ (m1_subset_1 @ X0 @ sk_B)
% 7.06/7.23          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 7.06/7.23              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.06/7.23          | (v1_xboole_0 @ sk_C))),
% 7.06/7.23      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 7.06/7.23  thf('96', plain, (~ (v1_xboole_0 @ sk_C)),
% 7.06/7.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.06/7.23  thf('97', plain,
% 7.06/7.23      (![X0 : $i]:
% 7.06/7.23         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 7.06/7.23            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.06/7.23          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 7.06/7.23      inference('clc', [status(thm)], ['95', '96'])).
% 7.06/7.23  thf('98', plain,
% 7.06/7.23      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 7.06/7.23         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.06/7.23      inference('sup-', [status(thm)], ['80', '97'])).
% 7.06/7.23  thf('99', plain,
% 7.06/7.23      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.06/7.23         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.06/7.23      inference('demod', [status(thm)], ['79', '98'])).
% 7.06/7.23  thf('100', plain,
% 7.06/7.23      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.06/7.23          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 7.06/7.23        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 7.06/7.23      inference('sup-', [status(thm)], ['78', '99'])).
% 7.06/7.23  thf('101', plain, (((k1_relat_1 @ sk_E) = (k1_xboole_0))),
% 7.06/7.23      inference('simplify', [status(thm)], ['100'])).
% 7.06/7.23  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.06/7.23      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.06/7.23  thf('103', plain, ($false),
% 7.06/7.23      inference('demod', [status(thm)], ['42', '101', '102'])).
% 7.06/7.23  
% 7.06/7.23  % SZS output end Refutation
% 7.06/7.23  
% 7.06/7.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0p4SbW21eY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:04 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 341 expanded)
%              Number of leaves         :   47 ( 122 expanded)
%              Depth                    :   20
%              Number of atoms          : 1323 (7352 expanded)
%              Number of equality atoms :   67 ( 315 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X38 ) @ X39 )
      | ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X38 ) @ X39 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['23','32','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['16','19','20','36'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('38',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('41',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X38 ) @ X39 )
      | ( v1_funct_2 @ X38 @ ( k1_relat_1 @ X38 ) @ X39 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['17','18'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['23','32','35'])).

thf('46',plain,(
    v1_funct_2 @ sk_D @ sk_B @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['5','48'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( ( k7_partfun1 @ X31 @ X30 @ X29 )
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('54',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_E )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['51','54','55'])).

thf('57',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','56'])).

thf('58',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X33 @ X34 @ X37 @ X32 @ X36 ) @ X35 )
        = ( k1_funct_1 @ X36 @ ( k1_funct_1 @ X32 @ X35 ) ) )
      | ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X33 @ X34 @ X32 ) @ ( k1_relset_1 @ X34 @ X37 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','69'])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['59','76'])).

thf('78',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['58','77'])).

thf('79',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_E )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['16','19','20','36'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('82',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ~ ( v1_xboole_0 @ C )
              & ( v1_funct_2 @ C @ A @ B ) ) ) ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['86','94'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('96',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('97',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0p4SbW21eY
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.19/1.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.19/1.39  % Solved by: fo/fo7.sh
% 1.19/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.39  % done 664 iterations in 0.936s
% 1.19/1.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.19/1.39  % SZS output start Refutation
% 1.19/1.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.19/1.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.19/1.39  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.19/1.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.19/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.19/1.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.19/1.39  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.19/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.19/1.39  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 1.19/1.39  thf(sk_C_type, type, sk_C: $i).
% 1.19/1.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.19/1.39  thf(sk_F_type, type, sk_F: $i).
% 1.19/1.39  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 1.19/1.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.19/1.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.19/1.39  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.19/1.39  thf(sk_E_type, type, sk_E: $i).
% 1.19/1.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.19/1.39  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.19/1.39  thf(sk_D_type, type, sk_D: $i).
% 1.19/1.39  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.19/1.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.19/1.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.39  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.19/1.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.39  thf(t186_funct_2, conjecture,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.19/1.39       ( ![D:$i]:
% 1.19/1.39         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.19/1.39             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.19/1.39           ( ![E:$i]:
% 1.19/1.39             ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.39                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.19/1.39               ( ![F:$i]:
% 1.19/1.39                 ( ( m1_subset_1 @ F @ B ) =>
% 1.19/1.39                   ( ( r1_tarski @
% 1.19/1.39                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.19/1.39                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.19/1.39                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.19/1.39                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.19/1.39                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.39    (~( ![A:$i,B:$i,C:$i]:
% 1.19/1.39        ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.19/1.39          ( ![D:$i]:
% 1.19/1.39            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.19/1.39                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.19/1.39              ( ![E:$i]:
% 1.19/1.39                ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.39                    ( m1_subset_1 @
% 1.19/1.39                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.19/1.39                  ( ![F:$i]:
% 1.19/1.39                    ( ( m1_subset_1 @ F @ B ) =>
% 1.19/1.39                      ( ( r1_tarski @
% 1.19/1.39                          ( k2_relset_1 @ B @ C @ D ) @ 
% 1.19/1.39                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.19/1.39                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.19/1.39                          ( ( k1_funct_1 @
% 1.19/1.39                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.19/1.39                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.19/1.39    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 1.19/1.39  thf('0', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(cc2_relset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.39       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.19/1.39  thf('1', plain,
% 1.19/1.39      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.19/1.39         ((v5_relat_1 @ X6 @ X8)
% 1.19/1.39          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.19/1.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.19/1.39  thf('2', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 1.19/1.39      inference('sup-', [status(thm)], ['0', '1'])).
% 1.19/1.39  thf('3', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(t2_subset, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ A @ B ) =>
% 1.19/1.39       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.19/1.39  thf('4', plain,
% 1.19/1.39      (![X1 : $i, X2 : $i]:
% 1.19/1.39         ((r2_hidden @ X1 @ X2)
% 1.19/1.39          | (v1_xboole_0 @ X2)
% 1.19/1.39          | ~ (m1_subset_1 @ X1 @ X2))),
% 1.19/1.39      inference('cnf', [status(esa)], [t2_subset])).
% 1.19/1.39  thf('5', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['3', '4'])).
% 1.19/1.39  thf('6', plain,
% 1.19/1.39      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.39        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('7', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(redefinition_k1_relset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.39       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.19/1.39  thf('8', plain,
% 1.19/1.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.19/1.39         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.19/1.39          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.19/1.39      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.19/1.39  thf('9', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.19/1.39      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.39  thf('10', plain,
% 1.19/1.39      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.19/1.39      inference('demod', [status(thm)], ['6', '9'])).
% 1.19/1.39  thf('11', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(redefinition_k2_relset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.39       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.19/1.39  thf('12', plain,
% 1.19/1.39      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.19/1.39         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.19/1.39          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.19/1.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.19/1.39  thf('13', plain,
% 1.19/1.39      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.19/1.39      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.39  thf('14', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.19/1.39      inference('demod', [status(thm)], ['10', '13'])).
% 1.19/1.39  thf(t4_funct_2, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.19/1.39       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.19/1.39         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 1.19/1.39           ( m1_subset_1 @
% 1.19/1.39             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 1.19/1.39  thf('15', plain,
% 1.19/1.39      (![X38 : $i, X39 : $i]:
% 1.19/1.39         (~ (r1_tarski @ (k2_relat_1 @ X38) @ X39)
% 1.19/1.39          | (m1_subset_1 @ X38 @ 
% 1.19/1.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X38) @ X39)))
% 1.19/1.39          | ~ (v1_funct_1 @ X38)
% 1.19/1.39          | ~ (v1_relat_1 @ X38))),
% 1.19/1.39      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.19/1.39  thf('16', plain,
% 1.19/1.39      ((~ (v1_relat_1 @ sk_D)
% 1.19/1.39        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.39        | (m1_subset_1 @ sk_D @ 
% 1.19/1.39           (k1_zfmisc_1 @ 
% 1.19/1.39            (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E)))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['14', '15'])).
% 1.19/1.39  thf('17', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(cc1_relset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.39       ( v1_relat_1 @ C ) ))).
% 1.19/1.39  thf('18', plain,
% 1.19/1.39      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.39         ((v1_relat_1 @ X3)
% 1.19/1.39          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.19/1.39      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.19/1.39  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.39      inference('sup-', [status(thm)], ['17', '18'])).
% 1.19/1.39  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(d1_funct_2, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.39       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.19/1.39           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.19/1.39             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.19/1.39         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.19/1.39           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.19/1.39             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.19/1.39  thf(zf_stmt_1, axiom,
% 1.19/1.39    (![C:$i,B:$i,A:$i]:
% 1.19/1.39     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.19/1.39       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.19/1.39  thf('22', plain,
% 1.19/1.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.19/1.39         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 1.19/1.39          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 1.19/1.39          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.19/1.39  thf('23', plain,
% 1.19/1.39      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 1.19/1.39        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['21', '22'])).
% 1.19/1.39  thf('24', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.19/1.39  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.19/1.39  thf(zf_stmt_4, axiom,
% 1.19/1.39    (![B:$i,A:$i]:
% 1.19/1.39     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.19/1.39       ( zip_tseitin_0 @ B @ A ) ))).
% 1.19/1.39  thf(zf_stmt_5, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.39       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.19/1.39         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.19/1.39           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.19/1.39             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.19/1.39  thf('25', plain,
% 1.19/1.39      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.19/1.39         (~ (zip_tseitin_0 @ X26 @ X27)
% 1.19/1.39          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 1.19/1.39          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.19/1.39  thf('26', plain,
% 1.19/1.39      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['24', '25'])).
% 1.19/1.39  thf('27', plain,
% 1.19/1.39      (![X21 : $i, X22 : $i]:
% 1.19/1.39         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.19/1.39  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.19/1.39  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.19/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.19/1.39  thf('29', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.19/1.39      inference('sup+', [status(thm)], ['27', '28'])).
% 1.19/1.39  thf('30', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('31', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 1.19/1.39      inference('sup-', [status(thm)], ['29', '30'])).
% 1.19/1.39  thf('32', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 1.19/1.39      inference('demod', [status(thm)], ['26', '31'])).
% 1.19/1.39  thf('33', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('34', plain,
% 1.19/1.39      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.19/1.39         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 1.19/1.39          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.19/1.39      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.19/1.39  thf('35', plain,
% 1.19/1.39      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.19/1.39      inference('sup-', [status(thm)], ['33', '34'])).
% 1.19/1.39  thf('36', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.19/1.39      inference('demod', [status(thm)], ['23', '32', '35'])).
% 1.19/1.39  thf('37', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ 
% 1.19/1.39        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E))))),
% 1.19/1.39      inference('demod', [status(thm)], ['16', '19', '20', '36'])).
% 1.19/1.39  thf(t7_funct_2, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i,D:$i]:
% 1.19/1.39     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.19/1.39         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.19/1.39       ( ( r2_hidden @ C @ A ) =>
% 1.19/1.39         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.19/1.39           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 1.19/1.39  thf('38', plain,
% 1.19/1.39      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X40 @ X41)
% 1.19/1.39          | ((X42) = (k1_xboole_0))
% 1.19/1.39          | ~ (v1_funct_1 @ X43)
% 1.19/1.39          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.19/1.39          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.19/1.39          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ X42))),
% 1.19/1.39      inference('cnf', [status(esa)], [t7_funct_2])).
% 1.19/1.39  thf('39', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 1.19/1.39          | ~ (v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))
% 1.19/1.39          | ~ (v1_funct_1 @ sk_D)
% 1.19/1.39          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.19/1.39          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.39  thf('40', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.19/1.39      inference('demod', [status(thm)], ['10', '13'])).
% 1.19/1.39  thf('41', plain,
% 1.19/1.39      (![X38 : $i, X39 : $i]:
% 1.19/1.39         (~ (r1_tarski @ (k2_relat_1 @ X38) @ X39)
% 1.19/1.39          | (v1_funct_2 @ X38 @ (k1_relat_1 @ X38) @ X39)
% 1.19/1.39          | ~ (v1_funct_1 @ X38)
% 1.19/1.39          | ~ (v1_relat_1 @ X38))),
% 1.19/1.39      inference('cnf', [status(esa)], [t4_funct_2])).
% 1.19/1.39  thf('42', plain,
% 1.19/1.39      ((~ (v1_relat_1 @ sk_D)
% 1.19/1.39        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.39        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['40', '41'])).
% 1.19/1.39  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.19/1.39      inference('sup-', [status(thm)], ['17', '18'])).
% 1.19/1.39  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('45', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 1.19/1.39      inference('demod', [status(thm)], ['23', '32', '35'])).
% 1.19/1.39  thf('46', plain, ((v1_funct_2 @ sk_D @ sk_B @ (k1_relat_1 @ sk_E))),
% 1.19/1.39      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 1.19/1.39  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('48', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 1.19/1.39          | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.19/1.39          | ~ (r2_hidden @ X0 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['39', '46', '47'])).
% 1.19/1.39  thf('49', plain,
% 1.19/1.39      (((v1_xboole_0 @ sk_B)
% 1.19/1.39        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.19/1.39        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['5', '48'])).
% 1.19/1.39  thf(d8_partfun1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.19/1.39       ( ![C:$i]:
% 1.19/1.39         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.19/1.39           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 1.19/1.39  thf('50', plain,
% 1.19/1.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.19/1.39         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 1.19/1.39          | ((k7_partfun1 @ X31 @ X30 @ X29) = (k1_funct_1 @ X30 @ X29))
% 1.19/1.39          | ~ (v1_funct_1 @ X30)
% 1.19/1.39          | ~ (v5_relat_1 @ X30 @ X31)
% 1.19/1.39          | ~ (v1_relat_1 @ X30))),
% 1.19/1.39      inference('cnf', [status(esa)], [d8_partfun1])).
% 1.19/1.39  thf('51', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.19/1.39          | (v1_xboole_0 @ sk_B)
% 1.19/1.39          | ~ (v1_relat_1 @ sk_E)
% 1.19/1.39          | ~ (v5_relat_1 @ sk_E @ X0)
% 1.19/1.39          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.39          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.19/1.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.19/1.39      inference('sup-', [status(thm)], ['49', '50'])).
% 1.19/1.39  thf('52', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('53', plain,
% 1.19/1.39      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.19/1.39         ((v1_relat_1 @ X3)
% 1.19/1.39          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.19/1.39      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.19/1.39  thf('54', plain, ((v1_relat_1 @ sk_E)),
% 1.19/1.39      inference('sup-', [status(thm)], ['52', '53'])).
% 1.19/1.39  thf('55', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('56', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.19/1.39          | (v1_xboole_0 @ sk_B)
% 1.19/1.39          | ~ (v5_relat_1 @ sk_E @ X0)
% 1.19/1.39          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.19/1.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.19/1.39      inference('demod', [status(thm)], ['51', '54', '55'])).
% 1.19/1.39  thf('57', plain,
% 1.19/1.39      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.19/1.39          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.19/1.39        | (v1_xboole_0 @ sk_B)
% 1.19/1.39        | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['2', '56'])).
% 1.19/1.39  thf('58', plain,
% 1.19/1.39      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.19/1.39         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('59', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('60', plain,
% 1.19/1.39      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.19/1.39      inference('sup-', [status(thm)], ['7', '8'])).
% 1.19/1.39  thf('61', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(t185_funct_2, axiom,
% 1.19/1.39    (![A:$i,B:$i,C:$i]:
% 1.19/1.39     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.19/1.39       ( ![D:$i]:
% 1.19/1.39         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.19/1.39             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.19/1.39           ( ![E:$i]:
% 1.19/1.39             ( ( ( v1_funct_1 @ E ) & 
% 1.19/1.39                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.19/1.39               ( ![F:$i]:
% 1.19/1.39                 ( ( m1_subset_1 @ F @ B ) =>
% 1.19/1.39                   ( ( r1_tarski @
% 1.19/1.39                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.19/1.39                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.19/1.39                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.19/1.39                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.19/1.39                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.39  thf('62', plain,
% 1.19/1.39      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.19/1.39         (~ (v1_funct_1 @ X32)
% 1.19/1.39          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 1.19/1.39          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.19/1.39          | ~ (m1_subset_1 @ X35 @ X33)
% 1.19/1.39          | ((k1_funct_1 @ (k8_funct_2 @ X33 @ X34 @ X37 @ X32 @ X36) @ X35)
% 1.19/1.39              = (k1_funct_1 @ X36 @ (k1_funct_1 @ X32 @ X35)))
% 1.19/1.39          | ((X33) = (k1_xboole_0))
% 1.19/1.39          | ~ (r1_tarski @ (k2_relset_1 @ X33 @ X34 @ X32) @ 
% 1.19/1.39               (k1_relset_1 @ X34 @ X37 @ X36))
% 1.19/1.39          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X37)))
% 1.19/1.39          | ~ (v1_funct_1 @ X36)
% 1.19/1.39          | (v1_xboole_0 @ X34))),
% 1.19/1.39      inference('cnf', [status(esa)], [t185_funct_2])).
% 1.19/1.39  thf('63', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         ((v1_xboole_0 @ sk_C)
% 1.19/1.39          | ~ (v1_funct_1 @ X0)
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.19/1.39          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 1.19/1.39               (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.19/1.39          | ((sk_B) = (k1_xboole_0))
% 1.19/1.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.19/1.39              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.19/1.39          | ~ (m1_subset_1 @ X2 @ sk_B)
% 1.19/1.39          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 1.19/1.39          | ~ (v1_funct_1 @ sk_D))),
% 1.19/1.39      inference('sup-', [status(thm)], ['61', '62'])).
% 1.19/1.39  thf('64', plain,
% 1.19/1.39      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.19/1.39      inference('sup-', [status(thm)], ['11', '12'])).
% 1.19/1.39  thf('65', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('67', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         ((v1_xboole_0 @ sk_C)
% 1.19/1.39          | ~ (v1_funct_1 @ X0)
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.19/1.39          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.19/1.39          | ((sk_B) = (k1_xboole_0))
% 1.19/1.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.19/1.39              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.19/1.39          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 1.19/1.39  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('69', plain,
% 1.19/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.19/1.39         ((v1_xboole_0 @ sk_C)
% 1.19/1.39          | ~ (v1_funct_1 @ X0)
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.19/1.39          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.19/1.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.19/1.39              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.19/1.39          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 1.19/1.39      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.19/1.39  thf('70', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.19/1.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 1.19/1.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.19/1.39          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 1.19/1.39          | ~ (v1_funct_1 @ sk_E)
% 1.19/1.39          | (v1_xboole_0 @ sk_C))),
% 1.19/1.39      inference('sup-', [status(thm)], ['60', '69'])).
% 1.19/1.39  thf('71', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.19/1.39      inference('demod', [status(thm)], ['10', '13'])).
% 1.19/1.39  thf('72', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('74', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (~ (m1_subset_1 @ X0 @ sk_B)
% 1.19/1.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 1.19/1.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.19/1.39          | (v1_xboole_0 @ sk_C))),
% 1.19/1.39      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 1.19/1.39  thf('75', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('76', plain,
% 1.19/1.39      (![X0 : $i]:
% 1.19/1.39         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 1.19/1.39            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.19/1.39          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 1.19/1.39      inference('clc', [status(thm)], ['74', '75'])).
% 1.19/1.39  thf('77', plain,
% 1.19/1.39      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.19/1.39         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['59', '76'])).
% 1.19/1.39  thf('78', plain,
% 1.19/1.39      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.19/1.39         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.19/1.39      inference('demod', [status(thm)], ['58', '77'])).
% 1.19/1.39  thf('79', plain,
% 1.19/1.39      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.19/1.39          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 1.19/1.39        | ((k1_relat_1 @ sk_E) = (k1_xboole_0))
% 1.19/1.39        | (v1_xboole_0 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['57', '78'])).
% 1.19/1.39  thf('80', plain,
% 1.19/1.39      (((v1_xboole_0 @ sk_B) | ((k1_relat_1 @ sk_E) = (k1_xboole_0)))),
% 1.19/1.39      inference('simplify', [status(thm)], ['79'])).
% 1.19/1.39  thf('81', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ 
% 1.19/1.39        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_E))))),
% 1.19/1.39      inference('demod', [status(thm)], ['16', '19', '20', '36'])).
% 1.19/1.39  thf(cc4_relset_1, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( v1_xboole_0 @ A ) =>
% 1.19/1.39       ( ![C:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.19/1.39           ( v1_xboole_0 @ C ) ) ) ))).
% 1.19/1.39  thf('82', plain,
% 1.19/1.39      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.39         (~ (v1_xboole_0 @ X9)
% 1.19/1.39          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 1.19/1.39          | (v1_xboole_0 @ X10))),
% 1.19/1.39      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.19/1.39  thf('83', plain,
% 1.19/1.39      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_E)))),
% 1.19/1.39      inference('sup-', [status(thm)], ['81', '82'])).
% 1.19/1.39  thf('84', plain,
% 1.19/1.39      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.19/1.39        | (v1_xboole_0 @ sk_B)
% 1.19/1.39        | (v1_xboole_0 @ sk_D))),
% 1.19/1.39      inference('sup-', [status(thm)], ['80', '83'])).
% 1.19/1.39  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.19/1.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.19/1.39  thf('86', plain, (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_D))),
% 1.19/1.39      inference('demod', [status(thm)], ['84', '85'])).
% 1.19/1.39  thf('87', plain,
% 1.19/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf(cc6_funct_2, axiom,
% 1.19/1.39    (![A:$i,B:$i]:
% 1.19/1.39     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 1.19/1.39       ( ![C:$i]:
% 1.19/1.39         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.19/1.39           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.19/1.39             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 1.19/1.39               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 1.19/1.39  thf('88', plain,
% 1.19/1.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.19/1.39         ((v1_xboole_0 @ X18)
% 1.19/1.39          | (v1_xboole_0 @ X19)
% 1.19/1.39          | ~ (v1_funct_1 @ X20)
% 1.19/1.39          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 1.19/1.39          | ~ (v1_xboole_0 @ X20)
% 1.19/1.39          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.19/1.39      inference('cnf', [status(esa)], [cc6_funct_2])).
% 1.19/1.39  thf('89', plain,
% 1.19/1.39      ((~ (v1_xboole_0 @ sk_D)
% 1.19/1.39        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 1.19/1.39        | ~ (v1_funct_1 @ sk_D)
% 1.19/1.39        | (v1_xboole_0 @ sk_C)
% 1.19/1.39        | (v1_xboole_0 @ sk_B))),
% 1.19/1.39      inference('sup-', [status(thm)], ['87', '88'])).
% 1.19/1.39  thf('90', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('92', plain,
% 1.19/1.39      ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 1.19/1.39      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.19/1.39  thf('93', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('94', plain, (((v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_D))),
% 1.19/1.39      inference('clc', [status(thm)], ['92', '93'])).
% 1.19/1.39  thf('95', plain, ((v1_xboole_0 @ sk_B)),
% 1.19/1.39      inference('clc', [status(thm)], ['86', '94'])).
% 1.19/1.39  thf(l13_xboole_0, axiom,
% 1.19/1.39    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.19/1.39  thf('96', plain,
% 1.19/1.39      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.19/1.39      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.19/1.39  thf('97', plain, (((sk_B) = (k1_xboole_0))),
% 1.19/1.39      inference('sup-', [status(thm)], ['95', '96'])).
% 1.19/1.39  thf('98', plain, (((sk_B) != (k1_xboole_0))),
% 1.19/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.39  thf('99', plain, ($false),
% 1.19/1.39      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 1.19/1.39  
% 1.19/1.39  % SZS output end Refutation
% 1.19/1.39  
% 1.19/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fG06fUImNd

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:52 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 125 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  642 (1462 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t176_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( k7_partfun1 @ B @ C @ D )
                      = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ X28 )
      | ( ( k3_funct_2 @ X28 @ X29 @ X27 @ X30 )
        = ( k1_funct_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
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

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( sk_B @ X1 ) @ X1 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['24','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['21','36','39'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k7_partfun1 @ X26 @ X25 @ X24 )
        = ( k1_funct_1 @ X25 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ X26 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','49'])).

thf('51',plain,
    ( ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['13','50'])).

thf('52',plain,(
    ( k1_funct_1 @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['10','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fG06fUImNd
% 0.14/0.36  % Computer   : n002.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:34:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 95 iterations in 0.243s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.53/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.53/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.72  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.72  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.53/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.53/0.72  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.53/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.53/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.72  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.53/0.72  thf(t176_funct_2, conjecture,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.53/0.72           ( ![C:$i]:
% 0.53/0.72             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.72                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.72               ( ![D:$i]:
% 0.53/0.72                 ( ( m1_subset_1 @ D @ A ) =>
% 0.53/0.72                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.53/0.72                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.72    (~( ![A:$i]:
% 0.53/0.72        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.53/0.72          ( ![B:$i]:
% 0.53/0.72            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.53/0.72              ( ![C:$i]:
% 0.53/0.72                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.72                    ( m1_subset_1 @
% 0.53/0.72                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.72                  ( ![D:$i]:
% 0.53/0.72                    ( ( m1_subset_1 @ D @ A ) =>
% 0.53/0.72                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.53/0.72                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.53/0.72  thf('0', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('1', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(redefinition_k3_funct_2, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.53/0.72         ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.53/0.72         ( m1_subset_1 @ D @ A ) ) =>
% 0.53/0.72       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.53/0.72          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.53/0.72          | ~ (v1_funct_1 @ X27)
% 0.53/0.72          | (v1_xboole_0 @ X28)
% 0.53/0.72          | ~ (m1_subset_1 @ X30 @ X28)
% 0.53/0.72          | ((k3_funct_2 @ X28 @ X29 @ X27 @ X30) = (k1_funct_1 @ X27 @ X30)))),
% 0.53/0.72      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.53/0.72  thf('3', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.53/0.72          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.53/0.72          | (v1_xboole_0 @ sk_A)
% 0.53/0.72          | ~ (v1_funct_1 @ sk_C)
% 0.53/0.72          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.72  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('5', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('6', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 0.53/0.72          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.53/0.72          | (v1_xboole_0 @ sk_A))),
% 0.53/0.72      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.53/0.72  thf('7', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('8', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.53/0.72          | ((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0)
% 0.53/0.72              = (k1_funct_1 @ sk_C @ X0)))),
% 0.53/0.72      inference('clc', [status(thm)], ['6', '7'])).
% 0.53/0.72  thf('9', plain,
% 0.53/0.72      (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.53/0.72      inference('sup-', [status(thm)], ['0', '8'])).
% 0.53/0.72  thf('10', plain,
% 0.53/0.72      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D)
% 0.53/0.72         != (k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(cc2_relset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.72       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.72         ((v5_relat_1 @ X10 @ X12)
% 0.53/0.72          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.53/0.72      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.72  thf('13', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.53/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.72  thf('14', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(t2_subset, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ A @ B ) =>
% 0.53/0.72       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.53/0.72  thf('15', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i]:
% 0.53/0.72         ((r2_hidden @ X2 @ X3)
% 0.53/0.72          | (v1_xboole_0 @ X3)
% 0.53/0.72          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_subset])).
% 0.53/0.72  thf('16', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.72  thf('17', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('18', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.53/0.72      inference('clc', [status(thm)], ['16', '17'])).
% 0.53/0.72  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(d1_funct_2, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.53/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.53/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.53/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_1, axiom,
% 0.53/0.72    (![C:$i,B:$i,A:$i]:
% 0.53/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.53/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.72  thf('20', plain,
% 0.53/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.72         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.53/0.72          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.53/0.72          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.72  thf('21', plain,
% 0.53/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.53/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.53/0.72  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.53/0.72  thf(zf_stmt_4, axiom,
% 0.53/0.72    (![B:$i,A:$i]:
% 0.53/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.53/0.72  thf(zf_stmt_5, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.53/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.53/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.53/0.72  thf('23', plain,
% 0.53/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.72         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.53/0.72          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.53/0.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.72  thf('24', plain,
% 0.53/0.72      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.53/0.72        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.53/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.72  thf('25', plain,
% 0.53/0.72      (![X16 : $i, X17 : $i]:
% 0.53/0.72         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.53/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.53/0.72  thf('26', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.53/0.72  thf('27', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.53/0.72      inference('sup+', [status(thm)], ['25', '26'])).
% 0.53/0.72  thf(existence_m1_subset_1, axiom,
% 0.53/0.72    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.53/0.72  thf('28', plain, (![X1 : $i]: (m1_subset_1 @ (sk_B @ X1) @ X1)),
% 0.53/0.72      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.53/0.72  thf('29', plain,
% 0.53/0.72      (![X2 : $i, X3 : $i]:
% 0.53/0.72         ((r2_hidden @ X2 @ X3)
% 0.53/0.72          | (v1_xboole_0 @ X3)
% 0.53/0.72          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_subset])).
% 0.53/0.72  thf('30', plain,
% 0.53/0.72      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.72  thf(t7_ordinal1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.72  thf('31', plain,
% 0.53/0.72      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 0.53/0.72      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.53/0.72  thf('32', plain,
% 0.53/0.72      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.72  thf('33', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['27', '32'])).
% 0.53/0.72  thf('34', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('35', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.53/0.72      inference('sup-', [status(thm)], ['33', '34'])).
% 0.53/0.72  thf('36', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.53/0.72      inference('demod', [status(thm)], ['24', '35'])).
% 0.53/0.72  thf('37', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i]:
% 0.53/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.53/0.72  thf('38', plain,
% 0.53/0.72      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.53/0.72         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.53/0.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.53/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.53/0.72  thf('39', plain,
% 0.53/0.72      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.53/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.53/0.72  thf('40', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.53/0.72      inference('demod', [status(thm)], ['21', '36', '39'])).
% 0.53/0.72  thf(d8_partfun1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.72       ( ![C:$i]:
% 0.53/0.72         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.53/0.72           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.53/0.72  thf('41', plain,
% 0.53/0.72      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X24 @ (k1_relat_1 @ X25))
% 0.53/0.72          | ((k7_partfun1 @ X26 @ X25 @ X24) = (k1_funct_1 @ X25 @ X24))
% 0.53/0.72          | ~ (v1_funct_1 @ X25)
% 0.53/0.72          | ~ (v5_relat_1 @ X25 @ X26)
% 0.53/0.72          | ~ (v1_relat_1 @ X25))),
% 0.53/0.72      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.53/0.72  thf('42', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.72          | ~ (v1_relat_1 @ sk_C)
% 0.53/0.72          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.53/0.72          | ~ (v1_funct_1 @ sk_C)
% 0.53/0.72          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['40', '41'])).
% 0.53/0.72  thf('43', plain,
% 0.53/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf(cc2_relat_1, axiom,
% 0.53/0.72    (![A:$i]:
% 0.53/0.72     ( ( v1_relat_1 @ A ) =>
% 0.53/0.72       ( ![B:$i]:
% 0.53/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.72  thf('44', plain,
% 0.53/0.72      (![X4 : $i, X5 : $i]:
% 0.53/0.72         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.53/0.72          | (v1_relat_1 @ X4)
% 0.53/0.72          | ~ (v1_relat_1 @ X5))),
% 0.53/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.72  thf('45', plain,
% 0.53/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C))),
% 0.53/0.72      inference('sup-', [status(thm)], ['43', '44'])).
% 0.53/0.72  thf(fc6_relat_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.72  thf('46', plain,
% 0.53/0.72      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.53/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.72  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.72      inference('demod', [status(thm)], ['45', '46'])).
% 0.53/0.72  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.72  thf('49', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.72          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.53/0.72          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['42', '47', '48'])).
% 0.53/0.72  thf('50', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.53/0.72          | ~ (v5_relat_1 @ sk_C @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['18', '49'])).
% 0.53/0.72  thf('51', plain,
% 0.53/0.72      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.53/0.72      inference('sup-', [status(thm)], ['13', '50'])).
% 0.53/0.72  thf('52', plain,
% 0.53/0.72      (((k1_funct_1 @ sk_C @ sk_D)
% 0.53/0.72         != (k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.53/0.72      inference('demod', [status(thm)], ['10', '51'])).
% 0.53/0.72  thf('53', plain, ($false),
% 0.53/0.72      inference('simplify_reflect-', [status(thm)], ['9', '52'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

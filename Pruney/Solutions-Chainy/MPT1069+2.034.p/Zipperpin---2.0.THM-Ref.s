%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BqaCSgVUeu

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:05 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 222 expanded)
%              Number of leaves         :   48 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          : 1159 (4303 expanded)
%              Number of equality atoms :   58 ( 182 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_F @ sk_B_1 ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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

thf('5',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ X38 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X38 @ X39 @ X42 @ X37 @ X41 ) @ X40 )
        = ( k1_funct_1 @ X41 @ ( k1_funct_1 @ X37 @ X40 ) ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X38 @ X39 @ X37 ) @ ( k1_relset_1 @ X39 @ X42 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C ),
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

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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

thf('49',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('54',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 ),
    inference(demod,[status(thm)],['50','59'])).

thf('61',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['47','60'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('62',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X10 @ X9 ) @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['33','67'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference(clc,[status(thm)],['68','78'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('80',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ X35 ) )
      | ( ( k7_partfun1 @ X36 @ X35 @ X34 )
        = ( k1_funct_1 @ X35 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v5_relat_1 @ X35 @ X36 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('87',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','86'])).

thf('88',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BqaCSgVUeu
% 0.15/0.38  % Computer   : n018.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 20:01:12 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 2.00/2.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.00/2.25  % Solved by: fo/fo7.sh
% 2.00/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.00/2.25  % done 1767 iterations in 1.789s
% 2.00/2.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.00/2.25  % SZS output start Refutation
% 2.00/2.25  thf(sk_C_type, type, sk_C: $i).
% 2.00/2.25  thf(sk_B_type, type, sk_B: $i > $i).
% 2.00/2.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.00/2.25  thf(sk_F_type, type, sk_F: $i).
% 2.00/2.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.00/2.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.00/2.25  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.00/2.25  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.00/2.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.00/2.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.00/2.25  thf(sk_E_type, type, sk_E: $i).
% 2.00/2.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.00/2.25  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.00/2.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.00/2.25  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 2.00/2.25  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.00/2.25  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.00/2.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.00/2.25  thf(sk_D_type, type, sk_D: $i).
% 2.00/2.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.00/2.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.00/2.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.00/2.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.00/2.25  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.00/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.00/2.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.00/2.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.00/2.25  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 2.00/2.25  thf(t186_funct_2, conjecture,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.00/2.25       ( ![D:$i]:
% 2.00/2.25         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.00/2.25             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.00/2.25           ( ![E:$i]:
% 2.00/2.25             ( ( ( v1_funct_1 @ E ) & 
% 2.00/2.25                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 2.00/2.25               ( ![F:$i]:
% 2.00/2.25                 ( ( m1_subset_1 @ F @ B ) =>
% 2.00/2.25                   ( ( r1_tarski @
% 2.00/2.25                       ( k2_relset_1 @ B @ C @ D ) @ 
% 2.00/2.25                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 2.00/2.25                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.00/2.25                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 2.00/2.25                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.00/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.00/2.25    (~( ![A:$i,B:$i,C:$i]:
% 2.00/2.25        ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.00/2.25          ( ![D:$i]:
% 2.00/2.25            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.00/2.25                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.00/2.25              ( ![E:$i]:
% 2.00/2.25                ( ( ( v1_funct_1 @ E ) & 
% 2.00/2.25                    ( m1_subset_1 @
% 2.00/2.25                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 2.00/2.25                  ( ![F:$i]:
% 2.00/2.25                    ( ( m1_subset_1 @ F @ B ) =>
% 2.00/2.25                      ( ( r1_tarski @
% 2.00/2.25                          ( k2_relset_1 @ B @ C @ D ) @ 
% 2.00/2.25                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 2.00/2.25                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.00/2.25                          ( ( k1_funct_1 @
% 2.00/2.25                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 2.00/2.25                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.00/2.25    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 2.00/2.25  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('1', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(redefinition_k1_relset_1, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.00/2.25       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.00/2.25  thf('2', plain,
% 2.00/2.25      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.00/2.25         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.00/2.25          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.00/2.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.00/2.25  thf('3', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.00/2.25      inference('sup-', [status(thm)], ['1', '2'])).
% 2.00/2.25  thf('4', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(t185_funct_2, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.00/2.25       ( ![D:$i]:
% 2.00/2.25         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.00/2.25             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.00/2.25           ( ![E:$i]:
% 2.00/2.25             ( ( ( v1_funct_1 @ E ) & 
% 2.00/2.25                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 2.00/2.25               ( ![F:$i]:
% 2.00/2.25                 ( ( m1_subset_1 @ F @ B ) =>
% 2.00/2.25                   ( ( r1_tarski @
% 2.00/2.25                       ( k2_relset_1 @ B @ C @ D ) @ 
% 2.00/2.25                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 2.00/2.25                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.00/2.25                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 2.00/2.25                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.00/2.25  thf('5', plain,
% 2.00/2.25      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.00/2.25         (~ (v1_funct_1 @ X37)
% 2.00/2.25          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.00/2.25          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.00/2.25          | ~ (m1_subset_1 @ X40 @ X38)
% 2.00/2.25          | ((k1_funct_1 @ (k8_funct_2 @ X38 @ X39 @ X42 @ X37 @ X41) @ X40)
% 2.00/2.25              = (k1_funct_1 @ X41 @ (k1_funct_1 @ X37 @ X40)))
% 2.00/2.25          | ((X38) = (k1_xboole_0))
% 2.00/2.25          | ~ (r1_tarski @ (k2_relset_1 @ X38 @ X39 @ X37) @ 
% 2.00/2.25               (k1_relset_1 @ X39 @ X42 @ X41))
% 2.00/2.25          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X42)))
% 2.00/2.25          | ~ (v1_funct_1 @ X41)
% 2.00/2.25          | (v1_xboole_0 @ X39))),
% 2.00/2.25      inference('cnf', [status(esa)], [t185_funct_2])).
% 2.00/2.25  thf('6', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((v1_xboole_0 @ sk_C)
% 2.00/2.25          | ~ (v1_funct_1 @ X0)
% 2.00/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 2.00/2.25          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ 
% 2.00/2.25               (k1_relset_1 @ sk_C @ X1 @ X0))
% 2.00/2.25          | ((sk_B_1) = (k1_xboole_0))
% 2.00/2.25          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 2.00/2.25              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 2.00/2.25          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 2.00/2.25          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 2.00/2.25          | ~ (v1_funct_1 @ sk_D))),
% 2.00/2.25      inference('sup-', [status(thm)], ['4', '5'])).
% 2.00/2.25  thf('7', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(redefinition_k2_relset_1, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.00/2.25       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.00/2.25  thf('8', plain,
% 2.00/2.25      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.00/2.25         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 2.00/2.25          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.00/2.25      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.00/2.25  thf('9', plain,
% 2.00/2.25      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.00/2.25      inference('sup-', [status(thm)], ['7', '8'])).
% 2.00/2.25  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('12', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((v1_xboole_0 @ sk_C)
% 2.00/2.25          | ~ (v1_funct_1 @ X0)
% 2.00/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 2.00/2.25          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 2.00/2.25          | ((sk_B_1) = (k1_xboole_0))
% 2.00/2.25          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 2.00/2.25              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 2.00/2.25          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 2.00/2.25      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 2.00/2.25  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('14', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((v1_xboole_0 @ sk_C)
% 2.00/2.25          | ~ (v1_funct_1 @ X0)
% 2.00/2.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 2.00/2.25          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 2.00/2.25          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 2.00/2.25              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 2.00/2.25          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 2.00/2.25      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 2.00/2.25  thf('15', plain,
% 2.00/2.25      (![X0 : $i]:
% 2.00/2.25         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 2.00/2.25          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 2.00/2.25          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ 
% 2.00/2.25              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 2.00/2.25          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 2.00/2.25          | ~ (v1_funct_1 @ sk_E)
% 2.00/2.25          | (v1_xboole_0 @ sk_C))),
% 2.00/2.25      inference('sup-', [status(thm)], ['3', '14'])).
% 2.00/2.25  thf('16', plain,
% 2.00/2.25      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ 
% 2.00/2.25        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('17', plain,
% 2.00/2.25      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.00/2.25      inference('sup-', [status(thm)], ['1', '2'])).
% 2.00/2.25  thf('18', plain,
% 2.00/2.25      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 2.00/2.25      inference('demod', [status(thm)], ['16', '17'])).
% 2.00/2.25  thf('19', plain,
% 2.00/2.25      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.00/2.25      inference('sup-', [status(thm)], ['7', '8'])).
% 2.00/2.25  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 2.00/2.25      inference('demod', [status(thm)], ['18', '19'])).
% 2.00/2.25  thf('21', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('23', plain,
% 2.00/2.25      (![X0 : $i]:
% 2.00/2.25         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 2.00/2.25          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ 
% 2.00/2.25              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 2.00/2.25          | (v1_xboole_0 @ sk_C))),
% 2.00/2.25      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 2.00/2.25  thf('24', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('25', plain,
% 2.00/2.25      (![X0 : $i]:
% 2.00/2.25         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 2.00/2.25            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 2.00/2.25          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 2.00/2.25      inference('clc', [status(thm)], ['23', '24'])).
% 2.00/2.25  thf('26', plain,
% 2.00/2.25      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 2.00/2.25         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.00/2.25      inference('sup-', [status(thm)], ['0', '25'])).
% 2.00/2.25  thf('27', plain,
% 2.00/2.25      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 2.00/2.25         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('28', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(cc2_relset_1, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.00/2.25       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.00/2.25  thf('29', plain,
% 2.00/2.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.00/2.25         ((v5_relat_1 @ X17 @ X19)
% 2.00/2.25          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.00/2.25      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.00/2.25  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 2.00/2.25      inference('sup-', [status(thm)], ['28', '29'])).
% 2.00/2.25  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(t2_subset, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( m1_subset_1 @ A @ B ) =>
% 2.00/2.25       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.00/2.25  thf('32', plain,
% 2.00/2.25      (![X5 : $i, X6 : $i]:
% 2.00/2.25         ((r2_hidden @ X5 @ X6)
% 2.00/2.25          | (v1_xboole_0 @ X6)
% 2.00/2.25          | ~ (m1_subset_1 @ X5 @ X6))),
% 2.00/2.25      inference('cnf', [status(esa)], [t2_subset])).
% 2.00/2.25  thf('33', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 2.00/2.25      inference('sup-', [status(thm)], ['31', '32'])).
% 2.00/2.25  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 2.00/2.25      inference('demod', [status(thm)], ['18', '19'])).
% 2.00/2.25  thf(d19_relat_1, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( v1_relat_1 @ B ) =>
% 2.00/2.25       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.00/2.25  thf('35', plain,
% 2.00/2.25      (![X7 : $i, X8 : $i]:
% 2.00/2.25         (~ (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 2.00/2.25          | (v5_relat_1 @ X7 @ X8)
% 2.00/2.25          | ~ (v1_relat_1 @ X7))),
% 2.00/2.25      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.00/2.25  thf('36', plain,
% 2.00/2.25      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 2.00/2.25      inference('sup-', [status(thm)], ['34', '35'])).
% 2.00/2.25  thf('37', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(cc1_relset_1, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.00/2.25       ( v1_relat_1 @ C ) ))).
% 2.00/2.25  thf('38', plain,
% 2.00/2.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.00/2.25         ((v1_relat_1 @ X14)
% 2.00/2.25          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.00/2.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.00/2.25  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 2.00/2.25      inference('sup-', [status(thm)], ['37', '38'])).
% 2.00/2.25  thf('40', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 2.00/2.25      inference('demod', [status(thm)], ['36', '39'])).
% 2.00/2.25  thf('41', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(d1_funct_2, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.00/2.25       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.00/2.25           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.00/2.25             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.00/2.25         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.00/2.25           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.00/2.25             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.00/2.25  thf(zf_stmt_1, axiom,
% 2.00/2.25    (![C:$i,B:$i,A:$i]:
% 2.00/2.25     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.00/2.25       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.00/2.25  thf('42', plain,
% 2.00/2.25      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.00/2.25         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 2.00/2.25          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 2.00/2.25          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.00/2.25  thf('43', plain,
% 2.00/2.25      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)
% 2.00/2.25        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D)))),
% 2.00/2.25      inference('sup-', [status(thm)], ['41', '42'])).
% 2.00/2.25  thf('44', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('45', plain,
% 2.00/2.25      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.00/2.25         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.00/2.25          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.00/2.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.00/2.25  thf('46', plain,
% 2.00/2.25      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.00/2.25      inference('sup-', [status(thm)], ['44', '45'])).
% 2.00/2.25  thf('47', plain,
% 2.00/2.25      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)
% 2.00/2.25        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 2.00/2.25      inference('demod', [status(thm)], ['43', '46'])).
% 2.00/2.25  thf('48', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.00/2.25  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.00/2.25  thf(zf_stmt_4, axiom,
% 2.00/2.25    (![B:$i,A:$i]:
% 2.00/2.25     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.00/2.25       ( zip_tseitin_0 @ B @ A ) ))).
% 2.00/2.25  thf(zf_stmt_5, axiom,
% 2.00/2.25    (![A:$i,B:$i,C:$i]:
% 2.00/2.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.00/2.25       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.00/2.25         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.00/2.25           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.00/2.25             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.00/2.25  thf('49', plain,
% 2.00/2.25      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.00/2.25         (~ (zip_tseitin_0 @ X31 @ X32)
% 2.00/2.25          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 2.00/2.25          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.00/2.25  thf('50', plain,
% 2.00/2.25      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)
% 2.00/2.25        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 2.00/2.25      inference('sup-', [status(thm)], ['48', '49'])).
% 2.00/2.25  thf('51', plain,
% 2.00/2.25      (![X26 : $i, X27 : $i]:
% 2.00/2.25         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.00/2.25  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.00/2.25  thf('52', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 2.00/2.25      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.00/2.25  thf('53', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.00/2.25         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 2.00/2.25      inference('sup+', [status(thm)], ['51', '52'])).
% 2.00/2.25  thf(d1_xboole_0, axiom,
% 2.00/2.25    (![A:$i]:
% 2.00/2.25     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.00/2.25  thf('54', plain,
% 2.00/2.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.00/2.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.00/2.25  thf(t7_ordinal1, axiom,
% 2.00/2.25    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.00/2.25  thf('55', plain,
% 2.00/2.25      (![X12 : $i, X13 : $i]:
% 2.00/2.25         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 2.00/2.25      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.00/2.25  thf('56', plain,
% 2.00/2.25      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 2.00/2.25      inference('sup-', [status(thm)], ['54', '55'])).
% 2.00/2.25  thf('57', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 2.00/2.25      inference('sup-', [status(thm)], ['53', '56'])).
% 2.00/2.25  thf('58', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('59', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 2.00/2.25      inference('sup-', [status(thm)], ['57', '58'])).
% 2.00/2.25  thf('60', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)),
% 2.00/2.25      inference('demod', [status(thm)], ['50', '59'])).
% 2.00/2.25  thf('61', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 2.00/2.25      inference('demod', [status(thm)], ['47', '60'])).
% 2.00/2.25  thf(t172_funct_1, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 2.00/2.25       ( ![C:$i]:
% 2.00/2.25         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 2.00/2.25           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 2.00/2.25  thf('62', plain,
% 2.00/2.25      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.00/2.25         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 2.00/2.25          | (r2_hidden @ (k1_funct_1 @ X10 @ X9) @ X11)
% 2.00/2.25          | ~ (v1_funct_1 @ X10)
% 2.00/2.25          | ~ (v5_relat_1 @ X10 @ X11)
% 2.00/2.25          | ~ (v1_relat_1 @ X10))),
% 2.00/2.25      inference('cnf', [status(esa)], [t172_funct_1])).
% 2.00/2.25  thf('63', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         (~ (r2_hidden @ X0 @ sk_B_1)
% 2.00/2.25          | ~ (v1_relat_1 @ sk_D)
% 2.00/2.25          | ~ (v5_relat_1 @ sk_D @ X1)
% 2.00/2.25          | ~ (v1_funct_1 @ sk_D)
% 2.00/2.25          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 2.00/2.25      inference('sup-', [status(thm)], ['61', '62'])).
% 2.00/2.25  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 2.00/2.25      inference('sup-', [status(thm)], ['37', '38'])).
% 2.00/2.25  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('66', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         (~ (r2_hidden @ X0 @ sk_B_1)
% 2.00/2.25          | ~ (v5_relat_1 @ sk_D @ X1)
% 2.00/2.25          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 2.00/2.25      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.00/2.25  thf('67', plain,
% 2.00/2.25      (![X0 : $i]:
% 2.00/2.25         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 2.00/2.25          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 2.00/2.25      inference('sup-', [status(thm)], ['40', '66'])).
% 2.00/2.25  thf('68', plain,
% 2.00/2.25      (((v1_xboole_0 @ sk_B_1)
% 2.00/2.25        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 2.00/2.25      inference('sup-', [status(thm)], ['33', '67'])).
% 2.00/2.25  thf(l13_xboole_0, axiom,
% 2.00/2.25    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.00/2.25  thf('69', plain,
% 2.00/2.25      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.00/2.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.00/2.25  thf('70', plain,
% 2.00/2.25      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.00/2.25      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.00/2.25  thf('71', plain,
% 2.00/2.25      (![X0 : $i, X1 : $i]:
% 2.00/2.25         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 2.00/2.25      inference('sup+', [status(thm)], ['69', '70'])).
% 2.00/2.25  thf('72', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('73', plain,
% 2.00/2.25      (![X0 : $i]:
% 2.00/2.25         (((X0) != (k1_xboole_0))
% 2.00/2.25          | ~ (v1_xboole_0 @ X0)
% 2.00/2.25          | ~ (v1_xboole_0 @ sk_B_1))),
% 2.00/2.25      inference('sup-', [status(thm)], ['71', '72'])).
% 2.00/2.25  thf('74', plain,
% 2.00/2.25      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.00/2.25      inference('simplify', [status(thm)], ['73'])).
% 2.00/2.25  thf('75', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 2.00/2.25      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.00/2.25  thf('76', plain,
% 2.00/2.25      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 2.00/2.25      inference('sup-', [status(thm)], ['54', '55'])).
% 2.00/2.25  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.00/2.25      inference('sup-', [status(thm)], ['75', '76'])).
% 2.00/2.25  thf('78', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.00/2.25      inference('demod', [status(thm)], ['74', '77'])).
% 2.00/2.25  thf('79', plain,
% 2.00/2.25      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 2.00/2.25      inference('clc', [status(thm)], ['68', '78'])).
% 2.00/2.25  thf(d8_partfun1, axiom,
% 2.00/2.25    (![A:$i,B:$i]:
% 2.00/2.25     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 2.00/2.25       ( ![C:$i]:
% 2.00/2.25         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 2.00/2.25           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 2.00/2.25  thf('80', plain,
% 2.00/2.25      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.00/2.25         (~ (r2_hidden @ X34 @ (k1_relat_1 @ X35))
% 2.00/2.25          | ((k7_partfun1 @ X36 @ X35 @ X34) = (k1_funct_1 @ X35 @ X34))
% 2.00/2.25          | ~ (v1_funct_1 @ X35)
% 2.00/2.25          | ~ (v5_relat_1 @ X35 @ X36)
% 2.00/2.25          | ~ (v1_relat_1 @ X35))),
% 2.00/2.25      inference('cnf', [status(esa)], [d8_partfun1])).
% 2.00/2.25  thf('81', plain,
% 2.00/2.25      (![X0 : $i]:
% 2.00/2.25         (~ (v1_relat_1 @ sk_E)
% 2.00/2.25          | ~ (v5_relat_1 @ sk_E @ X0)
% 2.00/2.25          | ~ (v1_funct_1 @ sk_E)
% 2.00/2.25          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 2.00/2.25              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 2.00/2.25      inference('sup-', [status(thm)], ['79', '80'])).
% 2.00/2.25  thf('82', plain,
% 2.00/2.25      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('83', plain,
% 2.00/2.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.00/2.25         ((v1_relat_1 @ X14)
% 2.00/2.25          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 2.00/2.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.00/2.25  thf('84', plain, ((v1_relat_1 @ sk_E)),
% 2.00/2.25      inference('sup-', [status(thm)], ['82', '83'])).
% 2.00/2.25  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 2.00/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.00/2.25  thf('86', plain,
% 2.00/2.25      (![X0 : $i]:
% 2.00/2.25         (~ (v5_relat_1 @ sk_E @ X0)
% 2.00/2.25          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 2.00/2.25              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 2.00/2.25      inference('demod', [status(thm)], ['81', '84', '85'])).
% 2.00/2.25  thf('87', plain,
% 2.00/2.25      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 2.00/2.25         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.00/2.25      inference('sup-', [status(thm)], ['30', '86'])).
% 2.00/2.25  thf('88', plain,
% 2.00/2.25      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 2.00/2.25         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.00/2.25      inference('demod', [status(thm)], ['27', '87'])).
% 2.00/2.25  thf('89', plain, ($false),
% 2.00/2.25      inference('simplify_reflect-', [status(thm)], ['26', '88'])).
% 2.00/2.25  
% 2.00/2.25  % SZS output end Refutation
% 2.00/2.25  
% 2.00/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

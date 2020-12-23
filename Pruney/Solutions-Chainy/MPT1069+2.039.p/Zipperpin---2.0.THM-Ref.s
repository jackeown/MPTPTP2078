%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.64252LqND9

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:06 EST 2020

% Result     : Theorem 32.00s
% Output     : Refutation 32.00s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 199 expanded)
%              Number of leaves         :   45 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          : 1143 (4102 expanded)
%              Number of equality atoms :   61 ( 178 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42 ) @ X41 )
        = ( k1_funct_1 @ X42 @ ( k1_funct_1 @ X38 @ X41 ) ) )
      | ( X39 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X39 @ X40 @ X38 ) @ ( k1_relset_1 @ X40 @ X43 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('35',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['33','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2 ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('43',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
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

thf('45',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['43','52','55'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('58',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('63',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('65',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['40','64'])).

thf('66',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('74',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( ( k7_partfun1 @ X37 @ X36 @ X35 )
        = ( k1_funct_1 @ X36 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('78',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['75','78','79'])).

thf('81',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','80'])).

thf('82',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.64252LqND9
% 0.16/0.38  % Computer   : n023.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 12:59:51 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 32.00/32.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 32.00/32.21  % Solved by: fo/fo7.sh
% 32.00/32.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.00/32.21  % done 6334 iterations in 31.746s
% 32.00/32.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 32.00/32.21  % SZS output start Refutation
% 32.00/32.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.00/32.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 32.00/32.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 32.00/32.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.00/32.21  thf(sk_C_2_type, type, sk_C_2: $i).
% 32.00/32.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 32.00/32.21  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 32.00/32.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 32.00/32.21  thf(sk_F_type, type, sk_F: $i).
% 32.00/32.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.00/32.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 32.00/32.21  thf(sk_B_type, type, sk_B: $i).
% 32.00/32.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.00/32.21  thf(sk_E_type, type, sk_E: $i).
% 32.00/32.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 32.00/32.21  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 32.00/32.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 32.00/32.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 32.00/32.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.00/32.21  thf(sk_D_2_type, type, sk_D_2: $i).
% 32.00/32.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 32.00/32.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 32.00/32.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 32.00/32.21  thf(sk_A_type, type, sk_A: $i).
% 32.00/32.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 32.00/32.21  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 32.00/32.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 32.00/32.21  thf(t186_funct_2, conjecture,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( ~( v1_xboole_0 @ C ) ) =>
% 32.00/32.21       ( ![D:$i]:
% 32.00/32.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 32.00/32.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 32.00/32.21           ( ![E:$i]:
% 32.00/32.21             ( ( ( v1_funct_1 @ E ) & 
% 32.00/32.21                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 32.00/32.21               ( ![F:$i]:
% 32.00/32.21                 ( ( m1_subset_1 @ F @ B ) =>
% 32.00/32.21                   ( ( r1_tarski @
% 32.00/32.21                       ( k2_relset_1 @ B @ C @ D ) @ 
% 32.00/32.21                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 32.00/32.21                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.00/32.21                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 32.00/32.21                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 32.00/32.21  thf(zf_stmt_0, negated_conjecture,
% 32.00/32.21    (~( ![A:$i,B:$i,C:$i]:
% 32.00/32.21        ( ( ~( v1_xboole_0 @ C ) ) =>
% 32.00/32.21          ( ![D:$i]:
% 32.00/32.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 32.00/32.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 32.00/32.21              ( ![E:$i]:
% 32.00/32.21                ( ( ( v1_funct_1 @ E ) & 
% 32.00/32.21                    ( m1_subset_1 @
% 32.00/32.21                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 32.00/32.21                  ( ![F:$i]:
% 32.00/32.21                    ( ( m1_subset_1 @ F @ B ) =>
% 32.00/32.21                      ( ( r1_tarski @
% 32.00/32.21                          ( k2_relset_1 @ B @ C @ D ) @ 
% 32.00/32.21                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 32.00/32.21                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.00/32.21                          ( ( k1_funct_1 @
% 32.00/32.21                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 32.00/32.21                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 32.00/32.21    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 32.00/32.21  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('1', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(redefinition_k1_relset_1, axiom,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.00/32.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 32.00/32.21  thf('2', plain,
% 32.00/32.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 32.00/32.21         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 32.00/32.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 32.00/32.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 32.00/32.21  thf('3', plain,
% 32.00/32.21      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 32.00/32.21      inference('sup-', [status(thm)], ['1', '2'])).
% 32.00/32.21  thf('4', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(t185_funct_2, axiom,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( ~( v1_xboole_0 @ C ) ) =>
% 32.00/32.21       ( ![D:$i]:
% 32.00/32.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 32.00/32.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 32.00/32.21           ( ![E:$i]:
% 32.00/32.21             ( ( ( v1_funct_1 @ E ) & 
% 32.00/32.21                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 32.00/32.21               ( ![F:$i]:
% 32.00/32.21                 ( ( m1_subset_1 @ F @ B ) =>
% 32.00/32.21                   ( ( r1_tarski @
% 32.00/32.21                       ( k2_relset_1 @ B @ C @ D ) @ 
% 32.00/32.21                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 32.00/32.21                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.00/32.21                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 32.00/32.21                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 32.00/32.21  thf('5', plain,
% 32.00/32.21      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 32.00/32.21         (~ (v1_funct_1 @ X38)
% 32.00/32.21          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 32.00/32.21          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 32.00/32.21          | ~ (m1_subset_1 @ X41 @ X39)
% 32.00/32.21          | ((k1_funct_1 @ (k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42) @ X41)
% 32.00/32.21              = (k1_funct_1 @ X42 @ (k1_funct_1 @ X38 @ X41)))
% 32.00/32.21          | ((X39) = (k1_xboole_0))
% 32.00/32.21          | ~ (r1_tarski @ (k2_relset_1 @ X39 @ X40 @ X38) @ 
% 32.00/32.21               (k1_relset_1 @ X40 @ X43 @ X42))
% 32.00/32.21          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X43)))
% 32.00/32.21          | ~ (v1_funct_1 @ X42)
% 32.00/32.21          | (v1_xboole_0 @ X40))),
% 32.00/32.21      inference('cnf', [status(esa)], [t185_funct_2])).
% 32.00/32.21  thf('6', plain,
% 32.00/32.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.00/32.21         ((v1_xboole_0 @ sk_C_2)
% 32.00/32.21          | ~ (v1_funct_1 @ X0)
% 32.00/32.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 32.00/32.21          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 32.00/32.21               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 32.00/32.21          | ((sk_B) = (k1_xboole_0))
% 32.00/32.21          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 32.00/32.21              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 32.00/32.21          | ~ (m1_subset_1 @ X2 @ sk_B)
% 32.00/32.21          | ~ (v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)
% 32.00/32.21          | ~ (v1_funct_1 @ sk_D_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['4', '5'])).
% 32.00/32.21  thf('7', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(redefinition_k2_relset_1, axiom,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.00/32.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 32.00/32.21  thf('8', plain,
% 32.00/32.21      (![X24 : $i, X25 : $i, X26 : $i]:
% 32.00/32.21         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 32.00/32.21          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 32.00/32.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.00/32.21  thf('9', plain,
% 32.00/32.21      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['7', '8'])).
% 32.00/32.21  thf('10', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('11', plain, ((v1_funct_1 @ sk_D_2)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('12', plain,
% 32.00/32.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.00/32.21         ((v1_xboole_0 @ sk_C_2)
% 32.00/32.21          | ~ (v1_funct_1 @ X0)
% 32.00/32.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 32.00/32.21          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 32.00/32.21               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 32.00/32.21          | ((sk_B) = (k1_xboole_0))
% 32.00/32.21          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 32.00/32.21              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 32.00/32.21          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 32.00/32.21      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 32.00/32.21  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('14', plain,
% 32.00/32.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.00/32.21         ((v1_xboole_0 @ sk_C_2)
% 32.00/32.21          | ~ (v1_funct_1 @ X0)
% 32.00/32.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 32.00/32.21          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 32.00/32.21               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 32.00/32.21          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 32.00/32.21              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 32.00/32.21          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 32.00/32.21      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 32.00/32.21  thf('15', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))
% 32.00/32.21          | ~ (m1_subset_1 @ X0 @ sk_B)
% 32.00/32.21          | ((k1_funct_1 @ 
% 32.00/32.21              (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 32.00/32.21              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 32.00/32.21          | ~ (m1_subset_1 @ sk_E @ 
% 32.00/32.21               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))
% 32.00/32.21          | ~ (v1_funct_1 @ sk_E)
% 32.00/32.21          | (v1_xboole_0 @ sk_C_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['3', '14'])).
% 32.00/32.21  thf('16', plain,
% 32.00/32.21      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 32.00/32.21        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('17', plain,
% 32.00/32.21      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 32.00/32.21      inference('sup-', [status(thm)], ['1', '2'])).
% 32.00/32.21  thf('18', plain,
% 32.00/32.21      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 32.00/32.21        (k1_relat_1 @ sk_E))),
% 32.00/32.21      inference('demod', [status(thm)], ['16', '17'])).
% 32.00/32.21  thf('19', plain,
% 32.00/32.21      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['7', '8'])).
% 32.00/32.21  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 32.00/32.21      inference('demod', [status(thm)], ['18', '19'])).
% 32.00/32.21  thf('21', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('23', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (~ (m1_subset_1 @ X0 @ sk_B)
% 32.00/32.21          | ((k1_funct_1 @ 
% 32.00/32.21              (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 32.00/32.21              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 32.00/32.21          | (v1_xboole_0 @ sk_C_2))),
% 32.00/32.21      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 32.00/32.21  thf('24', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('25', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 32.00/32.21            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 32.00/32.21          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 32.00/32.21      inference('clc', [status(thm)], ['23', '24'])).
% 32.00/32.21  thf('26', plain,
% 32.00/32.21      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 32.00/32.21         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 32.00/32.21      inference('sup-', [status(thm)], ['0', '25'])).
% 32.00/32.21  thf('27', plain,
% 32.00/32.21      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 32.00/32.21         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('28', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(cc2_relset_1, axiom,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.00/32.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 32.00/32.21  thf('29', plain,
% 32.00/32.21      (![X18 : $i, X19 : $i, X20 : $i]:
% 32.00/32.21         ((v5_relat_1 @ X18 @ X20)
% 32.00/32.21          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 32.00/32.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 32.00/32.21  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 32.00/32.21      inference('sup-', [status(thm)], ['28', '29'])).
% 32.00/32.21  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(t2_subset, axiom,
% 32.00/32.21    (![A:$i,B:$i]:
% 32.00/32.21     ( ( m1_subset_1 @ A @ B ) =>
% 32.00/32.21       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 32.00/32.21  thf('32', plain,
% 32.00/32.21      (![X6 : $i, X7 : $i]:
% 32.00/32.21         ((r2_hidden @ X6 @ X7)
% 32.00/32.21          | (v1_xboole_0 @ X7)
% 32.00/32.21          | ~ (m1_subset_1 @ X6 @ X7))),
% 32.00/32.21      inference('cnf', [status(esa)], [t2_subset])).
% 32.00/32.21  thf('33', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 32.00/32.21      inference('sup-', [status(thm)], ['31', '32'])).
% 32.00/32.21  thf(t8_boole, axiom,
% 32.00/32.21    (![A:$i,B:$i]:
% 32.00/32.21     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 32.00/32.21  thf('34', plain,
% 32.00/32.21      (![X4 : $i, X5 : $i]:
% 32.00/32.21         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 32.00/32.21      inference('cnf', [status(esa)], [t8_boole])).
% 32.00/32.21  thf('35', plain, (((sk_B) != (k1_xboole_0))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('36', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (((X0) != (k1_xboole_0))
% 32.00/32.21          | ~ (v1_xboole_0 @ sk_B)
% 32.00/32.21          | ~ (v1_xboole_0 @ X0))),
% 32.00/32.21      inference('sup-', [status(thm)], ['34', '35'])).
% 32.00/32.21  thf('37', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 32.00/32.21      inference('simplify', [status(thm)], ['36'])).
% 32.00/32.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 32.00/32.21  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 32.00/32.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 32.00/32.21  thf('39', plain, (~ (v1_xboole_0 @ sk_B)),
% 32.00/32.21      inference('simplify_reflect+', [status(thm)], ['37', '38'])).
% 32.00/32.21  thf('40', plain, ((r2_hidden @ sk_F @ sk_B)),
% 32.00/32.21      inference('clc', [status(thm)], ['33', '39'])).
% 32.00/32.21  thf('41', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(d1_funct_2, axiom,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.00/32.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 32.00/32.21           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 32.00/32.21             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 32.00/32.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 32.00/32.21           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 32.00/32.21             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 32.00/32.21  thf(zf_stmt_1, axiom,
% 32.00/32.21    (![C:$i,B:$i,A:$i]:
% 32.00/32.21     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 32.00/32.21       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 32.00/32.21  thf('42', plain,
% 32.00/32.21      (![X29 : $i, X30 : $i, X31 : $i]:
% 32.00/32.21         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 32.00/32.21          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 32.00/32.21          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 32.00/32.21  thf('43', plain,
% 32.00/32.21      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 32.00/32.21        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 32.00/32.21      inference('sup-', [status(thm)], ['41', '42'])).
% 32.00/32.21  thf('44', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 32.00/32.21  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 32.00/32.21  thf(zf_stmt_4, axiom,
% 32.00/32.21    (![B:$i,A:$i]:
% 32.00/32.21     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 32.00/32.21       ( zip_tseitin_0 @ B @ A ) ))).
% 32.00/32.21  thf(zf_stmt_5, axiom,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.00/32.21       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 32.00/32.21         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 32.00/32.21           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 32.00/32.21             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 32.00/32.21  thf('45', plain,
% 32.00/32.21      (![X32 : $i, X33 : $i, X34 : $i]:
% 32.00/32.21         (~ (zip_tseitin_0 @ X32 @ X33)
% 32.00/32.21          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 32.00/32.21          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 32.00/32.21  thf('46', plain,
% 32.00/32.21      (((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 32.00/32.21        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_B))),
% 32.00/32.21      inference('sup-', [status(thm)], ['44', '45'])).
% 32.00/32.21  thf('47', plain,
% 32.00/32.21      (![X27 : $i, X28 : $i]:
% 32.00/32.21         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 32.00/32.21  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 32.00/32.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 32.00/32.21  thf('49', plain,
% 32.00/32.21      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 32.00/32.21      inference('sup+', [status(thm)], ['47', '48'])).
% 32.00/32.21  thf('50', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('51', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_2 @ X0)),
% 32.00/32.21      inference('sup-', [status(thm)], ['49', '50'])).
% 32.00/32.21  thf('52', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)),
% 32.00/32.21      inference('demod', [status(thm)], ['46', '51'])).
% 32.00/32.21  thf('53', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('54', plain,
% 32.00/32.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 32.00/32.21         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 32.00/32.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 32.00/32.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 32.00/32.21  thf('55', plain,
% 32.00/32.21      (((k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['53', '54'])).
% 32.00/32.21  thf('56', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 32.00/32.21      inference('demod', [status(thm)], ['43', '52', '55'])).
% 32.00/32.21  thf(d5_funct_1, axiom,
% 32.00/32.21    (![A:$i]:
% 32.00/32.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.00/32.21       ( ![B:$i]:
% 32.00/32.21         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 32.00/32.21           ( ![C:$i]:
% 32.00/32.21             ( ( r2_hidden @ C @ B ) <=>
% 32.00/32.21               ( ?[D:$i]:
% 32.00/32.21                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 32.00/32.21                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 32.00/32.21  thf('57', plain,
% 32.00/32.21      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 32.00/32.21         (((X11) != (k2_relat_1 @ X9))
% 32.00/32.21          | (r2_hidden @ X13 @ X11)
% 32.00/32.21          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 32.00/32.21          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 32.00/32.21          | ~ (v1_funct_1 @ X9)
% 32.00/32.21          | ~ (v1_relat_1 @ X9))),
% 32.00/32.21      inference('cnf', [status(esa)], [d5_funct_1])).
% 32.00/32.21  thf('58', plain,
% 32.00/32.21      (![X9 : $i, X14 : $i]:
% 32.00/32.21         (~ (v1_relat_1 @ X9)
% 32.00/32.21          | ~ (v1_funct_1 @ X9)
% 32.00/32.21          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 32.00/32.21          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 32.00/32.21      inference('simplify', [status(thm)], ['57'])).
% 32.00/32.21  thf('59', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (~ (r2_hidden @ X0 @ sk_B)
% 32.00/32.21          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 32.00/32.21          | ~ (v1_funct_1 @ sk_D_2)
% 32.00/32.21          | ~ (v1_relat_1 @ sk_D_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['56', '58'])).
% 32.00/32.21  thf('60', plain, ((v1_funct_1 @ sk_D_2)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('61', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(cc1_relset_1, axiom,
% 32.00/32.21    (![A:$i,B:$i,C:$i]:
% 32.00/32.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.00/32.21       ( v1_relat_1 @ C ) ))).
% 32.00/32.21  thf('62', plain,
% 32.00/32.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 32.00/32.21         ((v1_relat_1 @ X15)
% 32.00/32.21          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 32.00/32.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.00/32.21  thf('63', plain, ((v1_relat_1 @ sk_D_2)),
% 32.00/32.21      inference('sup-', [status(thm)], ['61', '62'])).
% 32.00/32.21  thf('64', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (~ (r2_hidden @ X0 @ sk_B)
% 32.00/32.21          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 32.00/32.21      inference('demod', [status(thm)], ['59', '60', '63'])).
% 32.00/32.21  thf('65', plain,
% 32.00/32.21      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k2_relat_1 @ sk_D_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['40', '64'])).
% 32.00/32.21  thf('66', plain,
% 32.00/32.21      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 32.00/32.21        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf(d3_tarski, axiom,
% 32.00/32.21    (![A:$i,B:$i]:
% 32.00/32.21     ( ( r1_tarski @ A @ B ) <=>
% 32.00/32.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 32.00/32.21  thf('67', plain,
% 32.00/32.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.00/32.21         (~ (r2_hidden @ X0 @ X1)
% 32.00/32.21          | (r2_hidden @ X0 @ X2)
% 32.00/32.21          | ~ (r1_tarski @ X1 @ X2))),
% 32.00/32.21      inference('cnf', [status(esa)], [d3_tarski])).
% 32.00/32.21  thf('68', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))
% 32.00/32.21          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 32.00/32.21      inference('sup-', [status(thm)], ['66', '67'])).
% 32.00/32.21  thf('69', plain,
% 32.00/32.21      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 32.00/32.21      inference('sup-', [status(thm)], ['1', '2'])).
% 32.00/32.21  thf('70', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 32.00/32.21          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 32.00/32.21      inference('demod', [status(thm)], ['68', '69'])).
% 32.00/32.21  thf('71', plain,
% 32.00/32.21      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 32.00/32.21      inference('sup-', [status(thm)], ['7', '8'])).
% 32.00/32.21  thf('72', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 32.00/32.21          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 32.00/32.21      inference('demod', [status(thm)], ['70', '71'])).
% 32.00/32.21  thf('73', plain,
% 32.00/32.21      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))),
% 32.00/32.21      inference('sup-', [status(thm)], ['65', '72'])).
% 32.00/32.21  thf(d8_partfun1, axiom,
% 32.00/32.21    (![A:$i,B:$i]:
% 32.00/32.21     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 32.00/32.21       ( ![C:$i]:
% 32.00/32.21         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 32.00/32.21           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 32.00/32.21  thf('74', plain,
% 32.00/32.21      (![X35 : $i, X36 : $i, X37 : $i]:
% 32.00/32.21         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X36))
% 32.00/32.21          | ((k7_partfun1 @ X37 @ X36 @ X35) = (k1_funct_1 @ X36 @ X35))
% 32.00/32.21          | ~ (v1_funct_1 @ X36)
% 32.00/32.21          | ~ (v5_relat_1 @ X36 @ X37)
% 32.00/32.21          | ~ (v1_relat_1 @ X36))),
% 32.00/32.21      inference('cnf', [status(esa)], [d8_partfun1])).
% 32.00/32.21  thf('75', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (~ (v1_relat_1 @ sk_E)
% 32.00/32.21          | ~ (v5_relat_1 @ sk_E @ X0)
% 32.00/32.21          | ~ (v1_funct_1 @ sk_E)
% 32.00/32.21          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 32.00/32.21              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 32.00/32.21      inference('sup-', [status(thm)], ['73', '74'])).
% 32.00/32.21  thf('76', plain,
% 32.00/32.21      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('77', plain,
% 32.00/32.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 32.00/32.21         ((v1_relat_1 @ X15)
% 32.00/32.21          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 32.00/32.21      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.00/32.21  thf('78', plain, ((v1_relat_1 @ sk_E)),
% 32.00/32.21      inference('sup-', [status(thm)], ['76', '77'])).
% 32.00/32.21  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 32.00/32.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.00/32.21  thf('80', plain,
% 32.00/32.21      (![X0 : $i]:
% 32.00/32.21         (~ (v5_relat_1 @ sk_E @ X0)
% 32.00/32.21          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 32.00/32.21              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 32.00/32.21      inference('demod', [status(thm)], ['75', '78', '79'])).
% 32.00/32.21  thf('81', plain,
% 32.00/32.21      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 32.00/32.21         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 32.00/32.21      inference('sup-', [status(thm)], ['30', '80'])).
% 32.00/32.21  thf('82', plain,
% 32.00/32.21      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 32.00/32.21         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 32.00/32.21      inference('demod', [status(thm)], ['27', '81'])).
% 32.00/32.21  thf('83', plain, ($false),
% 32.00/32.21      inference('simplify_reflect-', [status(thm)], ['26', '82'])).
% 32.00/32.21  
% 32.00/32.21  % SZS output end Refutation
% 32.00/32.21  
% 32.00/32.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

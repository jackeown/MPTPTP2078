%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WB3oE5iMoE

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:06 EST 2020

% Result     : Theorem 29.04s
% Output     : Refutation 29.04s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 202 expanded)
%              Number of leaves         :   45 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          : 1151 (4115 expanded)
%              Number of equality atoms :   63 ( 181 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['33','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['45','54','57'])).

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

thf('59',plain,(
    ! [X8: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X10
       != ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( X12
       != ( k1_funct_1 @ X8 @ X13 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('60',plain,(
    ! [X8: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X8 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X13 ) @ ( k2_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['61','62','65'])).

thf('67',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['42','66'])).

thf('68',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relset_1 @ sk_C_2 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('76',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ X35 ) )
      | ( ( k7_partfun1 @ X36 @ X35 @ X34 )
        = ( k1_funct_1 @ X35 @ X34 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v5_relat_1 @ X35 @ X36 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('80',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['77','80','81'])).

thf('83',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','82'])).

thf('84',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D_2 @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','83'])).

thf('85',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WB3oE5iMoE
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.04/29.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 29.04/29.31  % Solved by: fo/fo7.sh
% 29.04/29.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.04/29.31  % done 6370 iterations in 28.854s
% 29.04/29.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 29.04/29.31  % SZS output start Refutation
% 29.04/29.31  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 29.04/29.31  thf(sk_F_type, type, sk_F: $i).
% 29.04/29.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 29.04/29.31  thf(sk_C_2_type, type, sk_C_2: $i).
% 29.04/29.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.04/29.31  thf(sk_E_type, type, sk_E: $i).
% 29.04/29.31  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 29.04/29.31  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 29.04/29.31  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 29.04/29.31  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 29.04/29.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 29.04/29.31  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 29.04/29.31  thf(sk_A_type, type, sk_A: $i).
% 29.04/29.31  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 29.04/29.31  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 29.04/29.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.04/29.31  thf(sk_B_type, type, sk_B: $i).
% 29.04/29.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.04/29.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 29.04/29.31  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 29.04/29.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.04/29.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 29.04/29.31  thf(sk_D_2_type, type, sk_D_2: $i).
% 29.04/29.31  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 29.04/29.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 29.04/29.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 29.04/29.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 29.04/29.31  thf(t186_funct_2, conjecture,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( ~( v1_xboole_0 @ C ) ) =>
% 29.04/29.31       ( ![D:$i]:
% 29.04/29.31         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 29.04/29.31             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 29.04/29.31           ( ![E:$i]:
% 29.04/29.31             ( ( ( v1_funct_1 @ E ) & 
% 29.04/29.31                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 29.04/29.31               ( ![F:$i]:
% 29.04/29.31                 ( ( m1_subset_1 @ F @ B ) =>
% 29.04/29.31                   ( ( r1_tarski @
% 29.04/29.31                       ( k2_relset_1 @ B @ C @ D ) @ 
% 29.04/29.31                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 29.04/29.31                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.04/29.31                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 29.04/29.31                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 29.04/29.31  thf(zf_stmt_0, negated_conjecture,
% 29.04/29.31    (~( ![A:$i,B:$i,C:$i]:
% 29.04/29.31        ( ( ~( v1_xboole_0 @ C ) ) =>
% 29.04/29.31          ( ![D:$i]:
% 29.04/29.31            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 29.04/29.31                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 29.04/29.31              ( ![E:$i]:
% 29.04/29.31                ( ( ( v1_funct_1 @ E ) & 
% 29.04/29.31                    ( m1_subset_1 @
% 29.04/29.31                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 29.04/29.31                  ( ![F:$i]:
% 29.04/29.31                    ( ( m1_subset_1 @ F @ B ) =>
% 29.04/29.31                      ( ( r1_tarski @
% 29.04/29.31                          ( k2_relset_1 @ B @ C @ D ) @ 
% 29.04/29.31                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 29.04/29.31                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.04/29.31                          ( ( k1_funct_1 @
% 29.04/29.31                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 29.04/29.31                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 29.04/29.31    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 29.04/29.31  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('1', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(redefinition_k1_relset_1, axiom,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.31       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 29.04/29.31  thf('2', plain,
% 29.04/29.31      (![X20 : $i, X21 : $i, X22 : $i]:
% 29.04/29.31         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 29.04/29.31          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 29.04/29.31      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.04/29.31  thf('3', plain,
% 29.04/29.31      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 29.04/29.31      inference('sup-', [status(thm)], ['1', '2'])).
% 29.04/29.31  thf('4', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(t185_funct_2, axiom,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( ~( v1_xboole_0 @ C ) ) =>
% 29.04/29.31       ( ![D:$i]:
% 29.04/29.31         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 29.04/29.31             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 29.04/29.31           ( ![E:$i]:
% 29.04/29.31             ( ( ( v1_funct_1 @ E ) & 
% 29.04/29.31                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 29.04/29.31               ( ![F:$i]:
% 29.04/29.31                 ( ( m1_subset_1 @ F @ B ) =>
% 29.04/29.31                   ( ( r1_tarski @
% 29.04/29.31                       ( k2_relset_1 @ B @ C @ D ) @ 
% 29.04/29.31                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 29.04/29.31                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.04/29.31                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 29.04/29.31                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 29.04/29.31  thf('5', plain,
% 29.04/29.31      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 29.04/29.31         (~ (v1_funct_1 @ X37)
% 29.04/29.31          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 29.04/29.31          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 29.04/29.31          | ~ (m1_subset_1 @ X40 @ X38)
% 29.04/29.31          | ((k1_funct_1 @ (k8_funct_2 @ X38 @ X39 @ X42 @ X37 @ X41) @ X40)
% 29.04/29.31              = (k1_funct_1 @ X41 @ (k1_funct_1 @ X37 @ X40)))
% 29.04/29.31          | ((X38) = (k1_xboole_0))
% 29.04/29.31          | ~ (r1_tarski @ (k2_relset_1 @ X38 @ X39 @ X37) @ 
% 29.04/29.31               (k1_relset_1 @ X39 @ X42 @ X41))
% 29.04/29.31          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X42)))
% 29.04/29.31          | ~ (v1_funct_1 @ X41)
% 29.04/29.31          | (v1_xboole_0 @ X39))),
% 29.04/29.31      inference('cnf', [status(esa)], [t185_funct_2])).
% 29.04/29.31  thf('6', plain,
% 29.04/29.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.31         ((v1_xboole_0 @ sk_C_2)
% 29.04/29.31          | ~ (v1_funct_1 @ X0)
% 29.04/29.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 29.04/29.31          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 29.04/29.31               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 29.04/29.31          | ((sk_B) = (k1_xboole_0))
% 29.04/29.31          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 29.04/29.31              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 29.04/29.31          | ~ (m1_subset_1 @ X2 @ sk_B)
% 29.04/29.31          | ~ (v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)
% 29.04/29.31          | ~ (v1_funct_1 @ sk_D_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['4', '5'])).
% 29.04/29.31  thf('7', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(redefinition_k2_relset_1, axiom,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.31       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 29.04/29.31  thf('8', plain,
% 29.04/29.31      (![X23 : $i, X24 : $i, X25 : $i]:
% 29.04/29.31         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 29.04/29.31          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 29.04/29.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 29.04/29.31  thf('9', plain,
% 29.04/29.31      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['7', '8'])).
% 29.04/29.31  thf('10', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('11', plain, ((v1_funct_1 @ sk_D_2)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('12', plain,
% 29.04/29.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.31         ((v1_xboole_0 @ sk_C_2)
% 29.04/29.31          | ~ (v1_funct_1 @ X0)
% 29.04/29.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 29.04/29.31          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 29.04/29.31               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 29.04/29.31          | ((sk_B) = (k1_xboole_0))
% 29.04/29.31          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 29.04/29.31              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 29.04/29.31          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 29.04/29.31      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 29.04/29.31  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('14', plain,
% 29.04/29.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.31         ((v1_xboole_0 @ sk_C_2)
% 29.04/29.31          | ~ (v1_funct_1 @ X0)
% 29.04/29.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ X1)))
% 29.04/29.31          | ~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ 
% 29.04/29.31               (k1_relset_1 @ sk_C_2 @ X1 @ X0))
% 29.04/29.31          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ X1 @ sk_D_2 @ X0) @ X2)
% 29.04/29.31              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D_2 @ X2)))
% 29.04/29.31          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 29.04/29.31      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 29.04/29.31  thf('15', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))
% 29.04/29.31          | ~ (m1_subset_1 @ X0 @ sk_B)
% 29.04/29.31          | ((k1_funct_1 @ 
% 29.04/29.31              (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 29.04/29.31              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 29.04/29.31          | ~ (m1_subset_1 @ sk_E @ 
% 29.04/29.31               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))
% 29.04/29.31          | ~ (v1_funct_1 @ sk_E)
% 29.04/29.31          | (v1_xboole_0 @ sk_C_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['3', '14'])).
% 29.04/29.31  thf('16', plain,
% 29.04/29.31      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 29.04/29.31        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('17', plain,
% 29.04/29.31      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 29.04/29.31      inference('sup-', [status(thm)], ['1', '2'])).
% 29.04/29.31  thf('18', plain,
% 29.04/29.31      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 29.04/29.31        (k1_relat_1 @ sk_E))),
% 29.04/29.31      inference('demod', [status(thm)], ['16', '17'])).
% 29.04/29.31  thf('19', plain,
% 29.04/29.31      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['7', '8'])).
% 29.04/29.31  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ (k1_relat_1 @ sk_E))),
% 29.04/29.31      inference('demod', [status(thm)], ['18', '19'])).
% 29.04/29.31  thf('21', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('23', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (~ (m1_subset_1 @ X0 @ sk_B)
% 29.04/29.31          | ((k1_funct_1 @ 
% 29.04/29.31              (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ X0)
% 29.04/29.31              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 29.04/29.31          | (v1_xboole_0 @ sk_C_2))),
% 29.04/29.31      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 29.04/29.31  thf('24', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('25', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 29.04/29.31            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ X0)))
% 29.04/29.31          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 29.04/29.31      inference('clc', [status(thm)], ['23', '24'])).
% 29.04/29.31  thf('26', plain,
% 29.04/29.31      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 29.04/29.31         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 29.04/29.31      inference('sup-', [status(thm)], ['0', '25'])).
% 29.04/29.31  thf('27', plain,
% 29.04/29.31      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 29.04/29.31         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('28', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(cc2_relset_1, axiom,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.31       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 29.04/29.31  thf('29', plain,
% 29.04/29.31      (![X17 : $i, X18 : $i, X19 : $i]:
% 29.04/29.31         ((v5_relat_1 @ X17 @ X19)
% 29.04/29.31          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 29.04/29.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.04/29.31  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 29.04/29.31      inference('sup-', [status(thm)], ['28', '29'])).
% 29.04/29.31  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(t2_subset, axiom,
% 29.04/29.31    (![A:$i,B:$i]:
% 29.04/29.31     ( ( m1_subset_1 @ A @ B ) =>
% 29.04/29.31       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 29.04/29.31  thf('32', plain,
% 29.04/29.31      (![X5 : $i, X6 : $i]:
% 29.04/29.31         ((r2_hidden @ X5 @ X6)
% 29.04/29.31          | (v1_xboole_0 @ X6)
% 29.04/29.31          | ~ (m1_subset_1 @ X5 @ X6))),
% 29.04/29.31      inference('cnf', [status(esa)], [t2_subset])).
% 29.04/29.31  thf('33', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 29.04/29.31      inference('sup-', [status(thm)], ['31', '32'])).
% 29.04/29.31  thf(l13_xboole_0, axiom,
% 29.04/29.31    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 29.04/29.31  thf('34', plain,
% 29.04/29.31      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 29.04/29.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 29.04/29.31  thf('35', plain,
% 29.04/29.31      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 29.04/29.31      inference('cnf', [status(esa)], [l13_xboole_0])).
% 29.04/29.31  thf('36', plain,
% 29.04/29.31      (![X0 : $i, X1 : $i]:
% 29.04/29.31         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 29.04/29.31      inference('sup+', [status(thm)], ['34', '35'])).
% 29.04/29.31  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('38', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (((X0) != (k1_xboole_0))
% 29.04/29.31          | ~ (v1_xboole_0 @ X0)
% 29.04/29.31          | ~ (v1_xboole_0 @ sk_B))),
% 29.04/29.31      inference('sup-', [status(thm)], ['36', '37'])).
% 29.04/29.31  thf('39', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 29.04/29.31      inference('simplify', [status(thm)], ['38'])).
% 29.04/29.31  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 29.04/29.31  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 29.04/29.31      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 29.04/29.31  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 29.04/29.31      inference('simplify_reflect+', [status(thm)], ['39', '40'])).
% 29.04/29.31  thf('42', plain, ((r2_hidden @ sk_F @ sk_B)),
% 29.04/29.31      inference('clc', [status(thm)], ['33', '41'])).
% 29.04/29.31  thf('43', plain, ((v1_funct_2 @ sk_D_2 @ sk_B @ sk_C_2)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(d1_funct_2, axiom,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.31       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 29.04/29.31           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 29.04/29.31             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 29.04/29.31         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 29.04/29.31           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 29.04/29.31             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 29.04/29.31  thf(zf_stmt_1, axiom,
% 29.04/29.31    (![C:$i,B:$i,A:$i]:
% 29.04/29.31     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 29.04/29.31       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 29.04/29.31  thf('44', plain,
% 29.04/29.31      (![X28 : $i, X29 : $i, X30 : $i]:
% 29.04/29.31         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 29.04/29.31          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 29.04/29.31          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_1])).
% 29.04/29.31  thf('45', plain,
% 29.04/29.31      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 29.04/29.31        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 29.04/29.31      inference('sup-', [status(thm)], ['43', '44'])).
% 29.04/29.31  thf('46', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 29.04/29.31  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 29.04/29.31  thf(zf_stmt_4, axiom,
% 29.04/29.31    (![B:$i,A:$i]:
% 29.04/29.31     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 29.04/29.31       ( zip_tseitin_0 @ B @ A ) ))).
% 29.04/29.31  thf(zf_stmt_5, axiom,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.31       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 29.04/29.31         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 29.04/29.31           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 29.04/29.31             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 29.04/29.31  thf('47', plain,
% 29.04/29.31      (![X31 : $i, X32 : $i, X33 : $i]:
% 29.04/29.31         (~ (zip_tseitin_0 @ X31 @ X32)
% 29.04/29.31          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 29.04/29.31          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_5])).
% 29.04/29.31  thf('48', plain,
% 29.04/29.31      (((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)
% 29.04/29.31        | ~ (zip_tseitin_0 @ sk_C_2 @ sk_B))),
% 29.04/29.31      inference('sup-', [status(thm)], ['46', '47'])).
% 29.04/29.31  thf('49', plain,
% 29.04/29.31      (![X26 : $i, X27 : $i]:
% 29.04/29.31         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_4])).
% 29.04/29.31  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 29.04/29.31      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 29.04/29.31  thf('51', plain,
% 29.04/29.31      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 29.04/29.31      inference('sup+', [status(thm)], ['49', '50'])).
% 29.04/29.31  thf('52', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('53', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_2 @ X0)),
% 29.04/29.31      inference('sup-', [status(thm)], ['51', '52'])).
% 29.04/29.31  thf('54', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_C_2 @ sk_B)),
% 29.04/29.31      inference('demod', [status(thm)], ['48', '53'])).
% 29.04/29.31  thf('55', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('56', plain,
% 29.04/29.31      (![X20 : $i, X21 : $i, X22 : $i]:
% 29.04/29.31         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 29.04/29.31          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 29.04/29.31      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.04/29.31  thf('57', plain,
% 29.04/29.31      (((k1_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['55', '56'])).
% 29.04/29.31  thf('58', plain, (((sk_B) = (k1_relat_1 @ sk_D_2))),
% 29.04/29.31      inference('demod', [status(thm)], ['45', '54', '57'])).
% 29.04/29.31  thf(d5_funct_1, axiom,
% 29.04/29.31    (![A:$i]:
% 29.04/29.31     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 29.04/29.31       ( ![B:$i]:
% 29.04/29.31         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 29.04/29.31           ( ![C:$i]:
% 29.04/29.31             ( ( r2_hidden @ C @ B ) <=>
% 29.04/29.31               ( ?[D:$i]:
% 29.04/29.31                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 29.04/29.31                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 29.04/29.31  thf('59', plain,
% 29.04/29.31      (![X8 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 29.04/29.31         (((X10) != (k2_relat_1 @ X8))
% 29.04/29.31          | (r2_hidden @ X12 @ X10)
% 29.04/29.31          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 29.04/29.31          | ((X12) != (k1_funct_1 @ X8 @ X13))
% 29.04/29.31          | ~ (v1_funct_1 @ X8)
% 29.04/29.31          | ~ (v1_relat_1 @ X8))),
% 29.04/29.31      inference('cnf', [status(esa)], [d5_funct_1])).
% 29.04/29.31  thf('60', plain,
% 29.04/29.31      (![X8 : $i, X13 : $i]:
% 29.04/29.31         (~ (v1_relat_1 @ X8)
% 29.04/29.31          | ~ (v1_funct_1 @ X8)
% 29.04/29.31          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X8))
% 29.04/29.31          | (r2_hidden @ (k1_funct_1 @ X8 @ X13) @ (k2_relat_1 @ X8)))),
% 29.04/29.31      inference('simplify', [status(thm)], ['59'])).
% 29.04/29.31  thf('61', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (~ (r2_hidden @ X0 @ sk_B)
% 29.04/29.31          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 29.04/29.31          | ~ (v1_funct_1 @ sk_D_2)
% 29.04/29.31          | ~ (v1_relat_1 @ sk_D_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['58', '60'])).
% 29.04/29.31  thf('62', plain, ((v1_funct_1 @ sk_D_2)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('63', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_2)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(cc1_relset_1, axiom,
% 29.04/29.31    (![A:$i,B:$i,C:$i]:
% 29.04/29.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.04/29.31       ( v1_relat_1 @ C ) ))).
% 29.04/29.31  thf('64', plain,
% 29.04/29.31      (![X14 : $i, X15 : $i, X16 : $i]:
% 29.04/29.31         ((v1_relat_1 @ X14)
% 29.04/29.31          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 29.04/29.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 29.04/29.31  thf('65', plain, ((v1_relat_1 @ sk_D_2)),
% 29.04/29.31      inference('sup-', [status(thm)], ['63', '64'])).
% 29.04/29.31  thf('66', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (~ (r2_hidden @ X0 @ sk_B)
% 29.04/29.31          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 29.04/29.31      inference('demod', [status(thm)], ['61', '62', '65'])).
% 29.04/29.31  thf('67', plain,
% 29.04/29.31      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k2_relat_1 @ sk_D_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['42', '66'])).
% 29.04/29.31  thf('68', plain,
% 29.04/29.31      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) @ 
% 29.04/29.31        (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf(d3_tarski, axiom,
% 29.04/29.31    (![A:$i,B:$i]:
% 29.04/29.31     ( ( r1_tarski @ A @ B ) <=>
% 29.04/29.31       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 29.04/29.31  thf('69', plain,
% 29.04/29.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.04/29.31         (~ (r2_hidden @ X0 @ X1)
% 29.04/29.31          | (r2_hidden @ X0 @ X2)
% 29.04/29.31          | ~ (r1_tarski @ X1 @ X2))),
% 29.04/29.31      inference('cnf', [status(esa)], [d3_tarski])).
% 29.04/29.31  thf('70', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_2 @ sk_A @ sk_E))
% 29.04/29.31          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 29.04/29.31      inference('sup-', [status(thm)], ['68', '69'])).
% 29.04/29.31  thf('71', plain,
% 29.04/29.31      (((k1_relset_1 @ sk_C_2 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 29.04/29.31      inference('sup-', [status(thm)], ['1', '2'])).
% 29.04/29.31  thf('72', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 29.04/29.31          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2)))),
% 29.04/29.31      inference('demod', [status(thm)], ['70', '71'])).
% 29.04/29.31  thf('73', plain,
% 29.04/29.31      (((k2_relset_1 @ sk_B @ sk_C_2 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 29.04/29.31      inference('sup-', [status(thm)], ['7', '8'])).
% 29.04/29.31  thf('74', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 29.04/29.31          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 29.04/29.31      inference('demod', [status(thm)], ['72', '73'])).
% 29.04/29.31  thf('75', plain,
% 29.04/29.31      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_F) @ (k1_relat_1 @ sk_E))),
% 29.04/29.31      inference('sup-', [status(thm)], ['67', '74'])).
% 29.04/29.31  thf(d8_partfun1, axiom,
% 29.04/29.31    (![A:$i,B:$i]:
% 29.04/29.31     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 29.04/29.31       ( ![C:$i]:
% 29.04/29.31         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 29.04/29.31           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 29.04/29.31  thf('76', plain,
% 29.04/29.31      (![X34 : $i, X35 : $i, X36 : $i]:
% 29.04/29.31         (~ (r2_hidden @ X34 @ (k1_relat_1 @ X35))
% 29.04/29.31          | ((k7_partfun1 @ X36 @ X35 @ X34) = (k1_funct_1 @ X35 @ X34))
% 29.04/29.31          | ~ (v1_funct_1 @ X35)
% 29.04/29.31          | ~ (v5_relat_1 @ X35 @ X36)
% 29.04/29.31          | ~ (v1_relat_1 @ X35))),
% 29.04/29.31      inference('cnf', [status(esa)], [d8_partfun1])).
% 29.04/29.31  thf('77', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (~ (v1_relat_1 @ sk_E)
% 29.04/29.31          | ~ (v5_relat_1 @ sk_E @ X0)
% 29.04/29.31          | ~ (v1_funct_1 @ sk_E)
% 29.04/29.31          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 29.04/29.31              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 29.04/29.31      inference('sup-', [status(thm)], ['75', '76'])).
% 29.04/29.31  thf('78', plain,
% 29.04/29.31      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_A)))),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('79', plain,
% 29.04/29.31      (![X14 : $i, X15 : $i, X16 : $i]:
% 29.04/29.31         ((v1_relat_1 @ X14)
% 29.04/29.31          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 29.04/29.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 29.04/29.31  thf('80', plain, ((v1_relat_1 @ sk_E)),
% 29.04/29.31      inference('sup-', [status(thm)], ['78', '79'])).
% 29.04/29.31  thf('81', plain, ((v1_funct_1 @ sk_E)),
% 29.04/29.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.04/29.31  thf('82', plain,
% 29.04/29.31      (![X0 : $i]:
% 29.04/29.31         (~ (v5_relat_1 @ sk_E @ X0)
% 29.04/29.31          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 29.04/29.31              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))))),
% 29.04/29.31      inference('demod', [status(thm)], ['77', '80', '81'])).
% 29.04/29.31  thf('83', plain,
% 29.04/29.31      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F))
% 29.04/29.31         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 29.04/29.31      inference('sup-', [status(thm)], ['30', '82'])).
% 29.04/29.31  thf('84', plain,
% 29.04/29.31      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_2 @ sk_A @ sk_D_2 @ sk_E) @ 
% 29.04/29.31         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D_2 @ sk_F)))),
% 29.04/29.31      inference('demod', [status(thm)], ['27', '83'])).
% 29.04/29.31  thf('85', plain, ($false),
% 29.04/29.31      inference('simplify_reflect-', [status(thm)], ['26', '84'])).
% 29.04/29.31  
% 29.04/29.31  % SZS output end Refutation
% 29.04/29.31  
% 29.04/29.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

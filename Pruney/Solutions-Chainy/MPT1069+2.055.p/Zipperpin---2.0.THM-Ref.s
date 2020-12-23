%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I0k4pyJpQy

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:08 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 225 expanded)
%              Number of leaves         :   48 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          : 1150 (4306 expanded)
%              Number of equality atoms :   59 ( 184 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_F @ sk_B_2 ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X36 @ X37 @ X40 @ X35 @ X39 ) @ X38 )
        = ( k1_funct_1 @ X39 @ ( k1_funct_1 @ X35 @ X38 ) ) )
      | ( X36 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X36 @ X37 @ X35 ) @ ( k1_relset_1 @ X37 @ X40 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_2 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_2 @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_C ),
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
      | ( sk_B_2 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B_2 @ sk_C @ sk_D )
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
      ( ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ sk_F @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('34',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ sk_F @ sk_B_2 ),
    inference(clc,[status(thm)],['33','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ sk_B_2 @ sk_C ),
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

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2 )
    | ( sk_B_2
      = ( k1_relset_1 @ sk_B_2 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_B_2 @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2 )
    | ( sk_B_2
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_2 @ sk_C ) ) ),
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

thf('62',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2 ),
    inference(demod,[status(thm)],['63','68'])).

thf('70',plain,
    ( sk_B_2
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['60','69'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('71',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X12 ) @ X14 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v5_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['50','51'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['53','75'])).

thf('77',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['44','76'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('78',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( ( k7_partfun1 @ X34 @ X33 @ X32 )
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['79','84','85'])).

thf('87',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','86'])).

thf('88',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I0k4pyJpQy
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:49:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 1.36/1.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.63  % Solved by: fo/fo7.sh
% 1.36/1.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.63  % done 1463 iterations in 1.189s
% 1.36/1.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.63  % SZS output start Refutation
% 1.36/1.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.36/1.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.36/1.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.63  thf(sk_F_type, type, sk_F: $i).
% 1.36/1.63  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.36/1.63  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 1.36/1.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.36/1.63  thf(sk_C_type, type, sk_C: $i).
% 1.36/1.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.36/1.63  thf(sk_E_type, type, sk_E: $i).
% 1.36/1.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.36/1.63  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.36/1.63  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.36/1.63  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.36/1.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.63  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.36/1.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.36/1.63  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.36/1.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.36/1.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.36/1.63  thf(sk_D_type, type, sk_D: $i).
% 1.36/1.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.36/1.63  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 1.36/1.63  thf(t186_funct_2, conjecture,
% 1.36/1.63    (![A:$i,B:$i,C:$i]:
% 1.36/1.63     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.36/1.63       ( ![D:$i]:
% 1.36/1.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.36/1.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.36/1.63           ( ![E:$i]:
% 1.36/1.63             ( ( ( v1_funct_1 @ E ) & 
% 1.36/1.63                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.36/1.63               ( ![F:$i]:
% 1.36/1.63                 ( ( m1_subset_1 @ F @ B ) =>
% 1.36/1.63                   ( ( r1_tarski @
% 1.36/1.63                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.36/1.63                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.36/1.63                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.36/1.63                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.36/1.63                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.36/1.63  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.63    (~( ![A:$i,B:$i,C:$i]:
% 1.36/1.63        ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.36/1.63          ( ![D:$i]:
% 1.36/1.63            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.36/1.63                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.36/1.63              ( ![E:$i]:
% 1.36/1.63                ( ( ( v1_funct_1 @ E ) & 
% 1.36/1.63                    ( m1_subset_1 @
% 1.36/1.63                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.36/1.63                  ( ![F:$i]:
% 1.36/1.63                    ( ( m1_subset_1 @ F @ B ) =>
% 1.36/1.63                      ( ( r1_tarski @
% 1.36/1.63                          ( k2_relset_1 @ B @ C @ D ) @ 
% 1.36/1.63                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.36/1.63                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.36/1.63                          ( ( k1_funct_1 @
% 1.36/1.63                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.36/1.63                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.36/1.63    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 1.36/1.63  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_2)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('1', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(redefinition_k1_relset_1, axiom,
% 1.36/1.63    (![A:$i,B:$i,C:$i]:
% 1.36/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.36/1.63  thf('2', plain,
% 1.36/1.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.36/1.63         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.36/1.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.36/1.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.36/1.63  thf('3', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.36/1.63      inference('sup-', [status(thm)], ['1', '2'])).
% 1.36/1.63  thf('4', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(t185_funct_2, axiom,
% 1.36/1.63    (![A:$i,B:$i,C:$i]:
% 1.36/1.63     ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.36/1.63       ( ![D:$i]:
% 1.36/1.63         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.36/1.63             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.36/1.63           ( ![E:$i]:
% 1.36/1.63             ( ( ( v1_funct_1 @ E ) & 
% 1.36/1.63                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 1.36/1.63               ( ![F:$i]:
% 1.36/1.63                 ( ( m1_subset_1 @ F @ B ) =>
% 1.36/1.63                   ( ( r1_tarski @
% 1.36/1.63                       ( k2_relset_1 @ B @ C @ D ) @ 
% 1.36/1.63                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 1.36/1.63                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.36/1.63                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 1.36/1.63                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.36/1.63  thf('5', plain,
% 1.36/1.63      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 1.36/1.63         (~ (v1_funct_1 @ X35)
% 1.36/1.63          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.36/1.63          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.36/1.63          | ~ (m1_subset_1 @ X38 @ X36)
% 1.36/1.63          | ((k1_funct_1 @ (k8_funct_2 @ X36 @ X37 @ X40 @ X35 @ X39) @ X38)
% 1.36/1.63              = (k1_funct_1 @ X39 @ (k1_funct_1 @ X35 @ X38)))
% 1.36/1.63          | ((X36) = (k1_xboole_0))
% 1.36/1.63          | ~ (r1_tarski @ (k2_relset_1 @ X36 @ X37 @ X35) @ 
% 1.36/1.63               (k1_relset_1 @ X37 @ X40 @ X39))
% 1.36/1.63          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X40)))
% 1.36/1.63          | ~ (v1_funct_1 @ X39)
% 1.36/1.63          | (v1_xboole_0 @ X37))),
% 1.36/1.63      inference('cnf', [status(esa)], [t185_funct_2])).
% 1.36/1.63  thf('6', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.63         ((v1_xboole_0 @ sk_C)
% 1.36/1.63          | ~ (v1_funct_1 @ X0)
% 1.36/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.36/1.63          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_2 @ sk_C @ sk_D) @ 
% 1.36/1.63               (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.36/1.63          | ((sk_B_2) = (k1_xboole_0))
% 1.36/1.63          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.36/1.63              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.36/1.63          | ~ (m1_subset_1 @ X2 @ sk_B_2)
% 1.36/1.63          | ~ (v1_funct_2 @ sk_D @ sk_B_2 @ sk_C)
% 1.36/1.63          | ~ (v1_funct_1 @ sk_D))),
% 1.36/1.63      inference('sup-', [status(thm)], ['4', '5'])).
% 1.36/1.63  thf('7', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(redefinition_k2_relset_1, axiom,
% 1.36/1.63    (![A:$i,B:$i,C:$i]:
% 1.36/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.36/1.63  thf('8', plain,
% 1.36/1.63      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.36/1.63         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.36/1.63          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.36/1.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.36/1.63  thf('9', plain,
% 1.36/1.63      (((k2_relset_1 @ sk_B_2 @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.36/1.63      inference('sup-', [status(thm)], ['7', '8'])).
% 1.36/1.63  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_C)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('12', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.63         ((v1_xboole_0 @ sk_C)
% 1.36/1.63          | ~ (v1_funct_1 @ X0)
% 1.36/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.36/1.63          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.36/1.63          | ((sk_B_2) = (k1_xboole_0))
% 1.36/1.63          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.36/1.63              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.36/1.63          | ~ (m1_subset_1 @ X2 @ sk_B_2))),
% 1.36/1.63      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 1.36/1.63  thf('13', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('14', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.63         ((v1_xboole_0 @ sk_C)
% 1.36/1.63          | ~ (v1_funct_1 @ X0)
% 1.36/1.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 1.36/1.63          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 1.36/1.63          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 1.36/1.63              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 1.36/1.63          | ~ (m1_subset_1 @ X2 @ sk_B_2))),
% 1.36/1.63      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 1.36/1.63  thf('15', plain,
% 1.36/1.63      (![X0 : $i]:
% 1.36/1.63         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 1.36/1.63          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 1.36/1.63          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E) @ 
% 1.36/1.63              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.36/1.63          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 1.36/1.63          | ~ (v1_funct_1 @ sk_E)
% 1.36/1.63          | (v1_xboole_0 @ sk_C))),
% 1.36/1.63      inference('sup-', [status(thm)], ['3', '14'])).
% 1.36/1.63  thf('16', plain,
% 1.36/1.63      ((r1_tarski @ (k2_relset_1 @ sk_B_2 @ sk_C @ sk_D) @ 
% 1.36/1.63        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('17', plain,
% 1.36/1.63      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.36/1.63      inference('sup-', [status(thm)], ['1', '2'])).
% 1.36/1.63  thf('18', plain,
% 1.36/1.63      ((r1_tarski @ (k2_relset_1 @ sk_B_2 @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.36/1.63      inference('demod', [status(thm)], ['16', '17'])).
% 1.36/1.63  thf('19', plain,
% 1.36/1.63      (((k2_relset_1 @ sk_B_2 @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.36/1.63      inference('sup-', [status(thm)], ['7', '8'])).
% 1.36/1.63  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.36/1.63      inference('demod', [status(thm)], ['18', '19'])).
% 1.36/1.63  thf('21', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('23', plain,
% 1.36/1.63      (![X0 : $i]:
% 1.36/1.63         (~ (m1_subset_1 @ X0 @ sk_B_2)
% 1.36/1.63          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E) @ 
% 1.36/1.63              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.36/1.63          | (v1_xboole_0 @ sk_C))),
% 1.36/1.63      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 1.36/1.63  thf('24', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('25', plain,
% 1.36/1.63      (![X0 : $i]:
% 1.36/1.63         (((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 1.36/1.63            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 1.36/1.63          | ~ (m1_subset_1 @ X0 @ sk_B_2))),
% 1.36/1.63      inference('clc', [status(thm)], ['23', '24'])).
% 1.36/1.63  thf('26', plain,
% 1.36/1.63      (((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.36/1.63         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.36/1.63      inference('sup-', [status(thm)], ['0', '25'])).
% 1.36/1.63  thf('27', plain,
% 1.36/1.63      (((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.36/1.63         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('28', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(cc2_relset_1, axiom,
% 1.36/1.63    (![A:$i,B:$i,C:$i]:
% 1.36/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.63       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.36/1.63  thf('29', plain,
% 1.36/1.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.36/1.63         ((v5_relat_1 @ X15 @ X17)
% 1.36/1.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.36/1.63      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.36/1.63  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 1.36/1.63      inference('sup-', [status(thm)], ['28', '29'])).
% 1.36/1.63  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B_2)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(t2_subset, axiom,
% 1.36/1.63    (![A:$i,B:$i]:
% 1.36/1.63     ( ( m1_subset_1 @ A @ B ) =>
% 1.36/1.63       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.36/1.63  thf('32', plain,
% 1.36/1.63      (![X4 : $i, X5 : $i]:
% 1.36/1.63         ((r2_hidden @ X4 @ X5)
% 1.36/1.63          | (v1_xboole_0 @ X5)
% 1.36/1.63          | ~ (m1_subset_1 @ X4 @ X5))),
% 1.36/1.63      inference('cnf', [status(esa)], [t2_subset])).
% 1.36/1.63  thf('33', plain, (((v1_xboole_0 @ sk_B_2) | (r2_hidden @ sk_F @ sk_B_2))),
% 1.36/1.63      inference('sup-', [status(thm)], ['31', '32'])).
% 1.36/1.63  thf(t7_xboole_0, axiom,
% 1.36/1.63    (![A:$i]:
% 1.36/1.63     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.36/1.63          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.36/1.63  thf('34', plain,
% 1.36/1.63      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 1.36/1.63      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.36/1.63  thf(d1_xboole_0, axiom,
% 1.36/1.63    (![A:$i]:
% 1.36/1.63     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.36/1.63  thf('35', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.36/1.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.63  thf('36', plain,
% 1.36/1.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.63      inference('sup-', [status(thm)], ['34', '35'])).
% 1.36/1.63  thf('37', plain,
% 1.36/1.63      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.63      inference('sup-', [status(thm)], ['34', '35'])).
% 1.36/1.63  thf('38', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i]:
% 1.36/1.63         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.36/1.63      inference('sup+', [status(thm)], ['36', '37'])).
% 1.36/1.63  thf('39', plain, (((sk_B_2) != (k1_xboole_0))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('40', plain,
% 1.36/1.63      (![X0 : $i]:
% 1.36/1.63         (((X0) != (k1_xboole_0))
% 1.36/1.63          | ~ (v1_xboole_0 @ X0)
% 1.36/1.63          | ~ (v1_xboole_0 @ sk_B_2))),
% 1.36/1.63      inference('sup-', [status(thm)], ['38', '39'])).
% 1.36/1.63  thf('41', plain,
% 1.36/1.63      ((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.36/1.63      inference('simplify', [status(thm)], ['40'])).
% 1.36/1.63  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.36/1.63  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.63  thf('43', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 1.36/1.63      inference('simplify_reflect+', [status(thm)], ['41', '42'])).
% 1.36/1.63  thf('44', plain, ((r2_hidden @ sk_F @ sk_B_2)),
% 1.36/1.63      inference('clc', [status(thm)], ['33', '43'])).
% 1.36/1.63  thf('45', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 1.36/1.63      inference('demod', [status(thm)], ['18', '19'])).
% 1.36/1.63  thf(d19_relat_1, axiom,
% 1.36/1.63    (![A:$i,B:$i]:
% 1.36/1.63     ( ( v1_relat_1 @ B ) =>
% 1.36/1.63       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.36/1.63  thf('46', plain,
% 1.36/1.63      (![X8 : $i, X9 : $i]:
% 1.36/1.63         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 1.36/1.63          | (v5_relat_1 @ X8 @ X9)
% 1.36/1.63          | ~ (v1_relat_1 @ X8))),
% 1.36/1.63      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.36/1.63  thf('47', plain,
% 1.36/1.63      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 1.36/1.63      inference('sup-', [status(thm)], ['45', '46'])).
% 1.36/1.63  thf('48', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(cc2_relat_1, axiom,
% 1.36/1.63    (![A:$i]:
% 1.36/1.63     ( ( v1_relat_1 @ A ) =>
% 1.36/1.63       ( ![B:$i]:
% 1.36/1.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.36/1.63  thf('49', plain,
% 1.36/1.63      (![X6 : $i, X7 : $i]:
% 1.36/1.63         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.36/1.63          | (v1_relat_1 @ X6)
% 1.36/1.63          | ~ (v1_relat_1 @ X7))),
% 1.36/1.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.36/1.63  thf('50', plain,
% 1.36/1.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)) | (v1_relat_1 @ sk_D))),
% 1.36/1.63      inference('sup-', [status(thm)], ['48', '49'])).
% 1.36/1.63  thf(fc6_relat_1, axiom,
% 1.36/1.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.36/1.63  thf('51', plain,
% 1.36/1.63      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 1.36/1.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.36/1.63  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 1.36/1.63      inference('demod', [status(thm)], ['50', '51'])).
% 1.36/1.63  thf('53', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 1.36/1.63      inference('demod', [status(thm)], ['47', '52'])).
% 1.36/1.63  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_B_2 @ sk_C)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(d1_funct_2, axiom,
% 1.36/1.63    (![A:$i,B:$i,C:$i]:
% 1.36/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.36/1.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.36/1.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.36/1.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.36/1.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.36/1.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.36/1.63  thf(zf_stmt_1, axiom,
% 1.36/1.63    (![C:$i,B:$i,A:$i]:
% 1.36/1.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.36/1.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.36/1.63  thf('55', plain,
% 1.36/1.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.36/1.63         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.36/1.63          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.36/1.63          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.36/1.63  thf('56', plain,
% 1.36/1.63      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2)
% 1.36/1.63        | ((sk_B_2) = (k1_relset_1 @ sk_B_2 @ sk_C @ sk_D)))),
% 1.36/1.63      inference('sup-', [status(thm)], ['54', '55'])).
% 1.36/1.63  thf('57', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('58', plain,
% 1.36/1.63      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.36/1.63         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.36/1.63          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.36/1.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.36/1.63  thf('59', plain,
% 1.36/1.63      (((k1_relset_1 @ sk_B_2 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.36/1.63      inference('sup-', [status(thm)], ['57', '58'])).
% 1.36/1.63  thf('60', plain,
% 1.36/1.63      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2)
% 1.36/1.63        | ((sk_B_2) = (k1_relat_1 @ sk_D)))),
% 1.36/1.63      inference('demod', [status(thm)], ['56', '59'])).
% 1.36/1.63  thf('61', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_2 @ sk_C)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.36/1.63  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.36/1.63  thf(zf_stmt_4, axiom,
% 1.36/1.63    (![B:$i,A:$i]:
% 1.36/1.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.36/1.63       ( zip_tseitin_0 @ B @ A ) ))).
% 1.36/1.63  thf(zf_stmt_5, axiom,
% 1.36/1.63    (![A:$i,B:$i,C:$i]:
% 1.36/1.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.36/1.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.36/1.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.36/1.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.36/1.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.36/1.63  thf('62', plain,
% 1.36/1.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.36/1.63         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.36/1.63          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.36/1.63          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.36/1.63  thf('63', plain,
% 1.36/1.63      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2)
% 1.36/1.63        | ~ (zip_tseitin_0 @ sk_C @ sk_B_2))),
% 1.36/1.63      inference('sup-', [status(thm)], ['61', '62'])).
% 1.36/1.63  thf('64', plain,
% 1.36/1.63      (![X24 : $i, X25 : $i]:
% 1.36/1.63         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.36/1.63  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.63      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.63  thf('66', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.36/1.63      inference('sup+', [status(thm)], ['64', '65'])).
% 1.36/1.63  thf('67', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('68', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 1.36/1.63      inference('sup-', [status(thm)], ['66', '67'])).
% 1.36/1.63  thf('69', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B_2)),
% 1.36/1.63      inference('demod', [status(thm)], ['63', '68'])).
% 1.36/1.63  thf('70', plain, (((sk_B_2) = (k1_relat_1 @ sk_D))),
% 1.36/1.63      inference('demod', [status(thm)], ['60', '69'])).
% 1.36/1.63  thf(t172_funct_1, axiom,
% 1.36/1.63    (![A:$i,B:$i]:
% 1.36/1.63     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.36/1.63       ( ![C:$i]:
% 1.36/1.63         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.36/1.63           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 1.36/1.63  thf('71', plain,
% 1.36/1.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.36/1.63         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 1.36/1.63          | (r2_hidden @ (k1_funct_1 @ X13 @ X12) @ X14)
% 1.36/1.63          | ~ (v1_funct_1 @ X13)
% 1.36/1.63          | ~ (v5_relat_1 @ X13 @ X14)
% 1.36/1.63          | ~ (v1_relat_1 @ X13))),
% 1.36/1.63      inference('cnf', [status(esa)], [t172_funct_1])).
% 1.36/1.63  thf('72', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i]:
% 1.36/1.63         (~ (r2_hidden @ X0 @ sk_B_2)
% 1.36/1.63          | ~ (v1_relat_1 @ sk_D)
% 1.36/1.63          | ~ (v5_relat_1 @ sk_D @ X1)
% 1.36/1.63          | ~ (v1_funct_1 @ sk_D)
% 1.36/1.63          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 1.36/1.63      inference('sup-', [status(thm)], ['70', '71'])).
% 1.36/1.63  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 1.36/1.63      inference('demod', [status(thm)], ['50', '51'])).
% 1.36/1.63  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('75', plain,
% 1.36/1.63      (![X0 : $i, X1 : $i]:
% 1.36/1.63         (~ (r2_hidden @ X0 @ sk_B_2)
% 1.36/1.63          | ~ (v5_relat_1 @ sk_D @ X1)
% 1.36/1.63          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 1.36/1.63      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.36/1.63  thf('76', plain,
% 1.36/1.63      (![X0 : $i]:
% 1.36/1.63         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 1.36/1.63          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 1.36/1.63      inference('sup-', [status(thm)], ['53', '75'])).
% 1.36/1.63  thf('77', plain,
% 1.36/1.63      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 1.36/1.63      inference('sup-', [status(thm)], ['44', '76'])).
% 1.36/1.63  thf(d8_partfun1, axiom,
% 1.36/1.63    (![A:$i,B:$i]:
% 1.36/1.63     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.36/1.63       ( ![C:$i]:
% 1.36/1.63         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.36/1.63           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 1.36/1.63  thf('78', plain,
% 1.36/1.63      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.36/1.63         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 1.36/1.63          | ((k7_partfun1 @ X34 @ X33 @ X32) = (k1_funct_1 @ X33 @ X32))
% 1.36/1.63          | ~ (v1_funct_1 @ X33)
% 1.36/1.63          | ~ (v5_relat_1 @ X33 @ X34)
% 1.36/1.63          | ~ (v1_relat_1 @ X33))),
% 1.36/1.63      inference('cnf', [status(esa)], [d8_partfun1])).
% 1.36/1.63  thf('79', plain,
% 1.36/1.63      (![X0 : $i]:
% 1.36/1.63         (~ (v1_relat_1 @ sk_E)
% 1.36/1.63          | ~ (v5_relat_1 @ sk_E @ X0)
% 1.36/1.63          | ~ (v1_funct_1 @ sk_E)
% 1.36/1.63          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.36/1.63              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.36/1.63      inference('sup-', [status(thm)], ['77', '78'])).
% 1.36/1.63  thf('80', plain,
% 1.36/1.63      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('81', plain,
% 1.36/1.63      (![X6 : $i, X7 : $i]:
% 1.36/1.63         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 1.36/1.63          | (v1_relat_1 @ X6)
% 1.36/1.63          | ~ (v1_relat_1 @ X7))),
% 1.36/1.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.36/1.63  thf('82', plain,
% 1.36/1.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 1.36/1.63      inference('sup-', [status(thm)], ['80', '81'])).
% 1.36/1.63  thf('83', plain,
% 1.36/1.63      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 1.36/1.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.36/1.63  thf('84', plain, ((v1_relat_1 @ sk_E)),
% 1.36/1.63      inference('demod', [status(thm)], ['82', '83'])).
% 1.36/1.63  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 1.36/1.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.63  thf('86', plain,
% 1.36/1.63      (![X0 : $i]:
% 1.36/1.63         (~ (v5_relat_1 @ sk_E @ X0)
% 1.36/1.63          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.36/1.63              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 1.36/1.63      inference('demod', [status(thm)], ['79', '84', '85'])).
% 1.36/1.63  thf('87', plain,
% 1.36/1.63      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 1.36/1.63         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.36/1.63      inference('sup-', [status(thm)], ['30', '86'])).
% 1.36/1.63  thf('88', plain,
% 1.36/1.63      (((k1_funct_1 @ (k8_funct_2 @ sk_B_2 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 1.36/1.63         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 1.36/1.63      inference('demod', [status(thm)], ['27', '87'])).
% 1.36/1.63  thf('89', plain, ($false),
% 1.36/1.63      inference('simplify_reflect-', [status(thm)], ['26', '88'])).
% 1.36/1.63  
% 1.36/1.63  % SZS output end Refutation
% 1.36/1.63  
% 1.46/1.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

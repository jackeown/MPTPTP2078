%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xblra6gPFR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:09 EST 2020

% Result     : Theorem 4.72s
% Output     : Refutation 4.72s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 231 expanded)
%              Number of leaves         :   47 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          : 1165 (4443 expanded)
%              Number of equality atoms :   58 ( 186 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ X35 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X35 @ X36 @ X39 @ X34 @ X38 ) @ X37 )
        = ( k1_funct_1 @ X38 @ ( k1_funct_1 @ X34 @ X37 ) ) )
      | ( X35 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X35 @ X36 @ X34 ) @ ( k1_relset_1 @ X36 @ X39 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
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
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
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
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
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
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['42','50'])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['58','67'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X13 @ X12 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','73'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('75',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X10 ) )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['39','78'])).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k1_relat_1 @ X32 ) )
      | ( ( k7_partfun1 @ X33 @ X32 @ X31 )
        = ( k1_funct_1 @ X32 @ X31 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v5_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['81','86','87'])).

thf('89',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','88'])).

thf('90',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','89'])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xblra6gPFR
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 4.72/4.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.72/4.91  % Solved by: fo/fo7.sh
% 4.72/4.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.72/4.91  % done 4059 iterations in 4.454s
% 4.72/4.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.72/4.91  % SZS output start Refutation
% 4.72/4.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.72/4.91  thf(sk_B_type, type, sk_B: $i).
% 4.72/4.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.72/4.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.72/4.91  thf(sk_E_type, type, sk_E: $i).
% 4.72/4.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.72/4.91  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 4.72/4.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.72/4.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.72/4.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.72/4.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.72/4.91  thf(sk_A_type, type, sk_A: $i).
% 4.72/4.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.72/4.91  thf(sk_C_type, type, sk_C: $i).
% 4.72/4.91  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 4.72/4.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.72/4.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.72/4.91  thf(sk_F_type, type, sk_F: $i).
% 4.72/4.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.72/4.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 4.72/4.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.72/4.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.72/4.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.72/4.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.72/4.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.72/4.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.72/4.91  thf(sk_D_type, type, sk_D: $i).
% 4.72/4.91  thf(t186_funct_2, conjecture,
% 4.72/4.91    (![A:$i,B:$i,C:$i]:
% 4.72/4.91     ( ( ~( v1_xboole_0 @ C ) ) =>
% 4.72/4.91       ( ![D:$i]:
% 4.72/4.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 4.72/4.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.72/4.91           ( ![E:$i]:
% 4.72/4.91             ( ( ( v1_funct_1 @ E ) & 
% 4.72/4.91                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 4.72/4.91               ( ![F:$i]:
% 4.72/4.91                 ( ( m1_subset_1 @ F @ B ) =>
% 4.72/4.91                   ( ( r1_tarski @
% 4.72/4.91                       ( k2_relset_1 @ B @ C @ D ) @ 
% 4.72/4.91                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 4.72/4.91                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.72/4.91                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 4.72/4.91                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.72/4.91  thf(zf_stmt_0, negated_conjecture,
% 4.72/4.91    (~( ![A:$i,B:$i,C:$i]:
% 4.72/4.91        ( ( ~( v1_xboole_0 @ C ) ) =>
% 4.72/4.91          ( ![D:$i]:
% 4.72/4.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 4.72/4.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.72/4.91              ( ![E:$i]:
% 4.72/4.91                ( ( ( v1_funct_1 @ E ) & 
% 4.72/4.91                    ( m1_subset_1 @
% 4.72/4.91                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 4.72/4.91                  ( ![F:$i]:
% 4.72/4.91                    ( ( m1_subset_1 @ F @ B ) =>
% 4.72/4.91                      ( ( r1_tarski @
% 4.72/4.91                          ( k2_relset_1 @ B @ C @ D ) @ 
% 4.72/4.91                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 4.72/4.91                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.72/4.91                          ( ( k1_funct_1 @
% 4.72/4.91                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 4.72/4.91                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 4.72/4.91    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 4.72/4.91  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 4.72/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.91  thf('1', plain,
% 4.72/4.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.72/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.91  thf(redefinition_k1_relset_1, axiom,
% 4.72/4.91    (![A:$i,B:$i,C:$i]:
% 4.72/4.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.72/4.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.72/4.91  thf('2', plain,
% 4.72/4.91      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.72/4.91         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 4.72/4.91          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.72/4.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.72/4.91  thf('3', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 4.72/4.91      inference('sup-', [status(thm)], ['1', '2'])).
% 4.72/4.91  thf('4', plain,
% 4.72/4.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.72/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.91  thf(t185_funct_2, axiom,
% 4.72/4.91    (![A:$i,B:$i,C:$i]:
% 4.72/4.91     ( ( ~( v1_xboole_0 @ C ) ) =>
% 4.72/4.91       ( ![D:$i]:
% 4.72/4.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 4.72/4.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 4.72/4.91           ( ![E:$i]:
% 4.72/4.91             ( ( ( v1_funct_1 @ E ) & 
% 4.72/4.91                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 4.72/4.91               ( ![F:$i]:
% 4.72/4.91                 ( ( m1_subset_1 @ F @ B ) =>
% 4.72/4.91                   ( ( r1_tarski @
% 4.72/4.91                       ( k2_relset_1 @ B @ C @ D ) @ 
% 4.72/4.91                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 4.72/4.91                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.72/4.91                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 4.72/4.91                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.72/4.91  thf('5', plain,
% 4.72/4.91      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 4.72/4.91         (~ (v1_funct_1 @ X34)
% 4.72/4.91          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 4.72/4.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 4.72/4.91          | ~ (m1_subset_1 @ X37 @ X35)
% 4.72/4.91          | ((k1_funct_1 @ (k8_funct_2 @ X35 @ X36 @ X39 @ X34 @ X38) @ X37)
% 4.72/4.91              = (k1_funct_1 @ X38 @ (k1_funct_1 @ X34 @ X37)))
% 4.72/4.91          | ((X35) = (k1_xboole_0))
% 4.72/4.91          | ~ (r1_tarski @ (k2_relset_1 @ X35 @ X36 @ X34) @ 
% 4.72/4.91               (k1_relset_1 @ X36 @ X39 @ X38))
% 4.72/4.91          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X39)))
% 4.72/4.91          | ~ (v1_funct_1 @ X38)
% 4.72/4.91          | (v1_xboole_0 @ X36))),
% 4.72/4.91      inference('cnf', [status(esa)], [t185_funct_2])).
% 4.72/4.91  thf('6', plain,
% 4.72/4.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.72/4.91         ((v1_xboole_0 @ sk_C)
% 4.72/4.91          | ~ (v1_funct_1 @ X0)
% 4.72/4.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 4.72/4.91          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 4.72/4.91               (k1_relset_1 @ sk_C @ X1 @ X0))
% 4.72/4.91          | ((sk_B) = (k1_xboole_0))
% 4.72/4.91          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 4.72/4.91              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 4.72/4.91          | ~ (m1_subset_1 @ X2 @ sk_B)
% 4.72/4.91          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 4.72/4.91          | ~ (v1_funct_1 @ sk_D))),
% 4.72/4.91      inference('sup-', [status(thm)], ['4', '5'])).
% 4.72/4.91  thf('7', plain,
% 4.72/4.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.72/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.91  thf(redefinition_k2_relset_1, axiom,
% 4.72/4.91    (![A:$i,B:$i,C:$i]:
% 4.72/4.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.72/4.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.72/4.91  thf('8', plain,
% 4.72/4.91      (![X20 : $i, X21 : $i, X22 : $i]:
% 4.72/4.91         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 4.72/4.91          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 4.72/4.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.72/4.91  thf('9', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.72/4.91      inference('sup-', [status(thm)], ['7', '8'])).
% 4.72/4.91  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 4.72/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.91  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 4.72/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.91  thf('12', plain,
% 4.72/4.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.72/4.91         ((v1_xboole_0 @ sk_C)
% 4.72/4.91          | ~ (v1_funct_1 @ X0)
% 4.72/4.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 4.72/4.91          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 4.72/4.91          | ((sk_B) = (k1_xboole_0))
% 4.72/4.91          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 4.72/4.91              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 4.72/4.91          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 4.72/4.91      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 4.72/4.91  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 4.72/4.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.91  thf('14', plain,
% 4.72/4.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.72/4.92         ((v1_xboole_0 @ sk_C)
% 4.72/4.92          | ~ (v1_funct_1 @ X0)
% 4.72/4.92          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 4.72/4.92          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 4.72/4.92          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 4.72/4.92              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 4.72/4.92          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 4.72/4.92      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 4.72/4.92  thf('15', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 4.72/4.92          | ~ (m1_subset_1 @ X0 @ sk_B)
% 4.72/4.92          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 4.72/4.92              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 4.72/4.92          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 4.72/4.92          | ~ (v1_funct_1 @ sk_E)
% 4.72/4.92          | (v1_xboole_0 @ sk_C))),
% 4.72/4.92      inference('sup-', [status(thm)], ['3', '14'])).
% 4.72/4.92  thf('16', plain,
% 4.72/4.92      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 4.72/4.92        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('17', plain,
% 4.72/4.92      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 4.72/4.92      inference('sup-', [status(thm)], ['1', '2'])).
% 4.72/4.92  thf('18', plain,
% 4.72/4.92      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 4.72/4.92      inference('demod', [status(thm)], ['16', '17'])).
% 4.72/4.92  thf('19', plain,
% 4.72/4.92      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 4.72/4.92      inference('sup-', [status(thm)], ['7', '8'])).
% 4.72/4.92  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 4.72/4.92      inference('demod', [status(thm)], ['18', '19'])).
% 4.72/4.92  thf('21', plain,
% 4.72/4.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('23', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (m1_subset_1 @ X0 @ sk_B)
% 4.72/4.92          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 4.72/4.92              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 4.72/4.92          | (v1_xboole_0 @ sk_C))),
% 4.72/4.92      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 4.72/4.92  thf('24', plain, (~ (v1_xboole_0 @ sk_C)),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('25', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 4.72/4.92            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 4.72/4.92          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 4.72/4.92      inference('clc', [status(thm)], ['23', '24'])).
% 4.72/4.92  thf('26', plain,
% 4.72/4.92      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 4.72/4.92         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 4.72/4.92      inference('sup-', [status(thm)], ['0', '25'])).
% 4.72/4.92  thf('27', plain,
% 4.72/4.92      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 4.72/4.92         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('28', plain,
% 4.72/4.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf(cc2_relset_1, axiom,
% 4.72/4.92    (![A:$i,B:$i,C:$i]:
% 4.72/4.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.72/4.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.72/4.92  thf('29', plain,
% 4.72/4.92      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.72/4.92         ((v5_relat_1 @ X14 @ X16)
% 4.72/4.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 4.72/4.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.72/4.92  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 4.72/4.92      inference('sup-', [status(thm)], ['28', '29'])).
% 4.72/4.92  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 4.72/4.92      inference('demod', [status(thm)], ['18', '19'])).
% 4.72/4.92  thf(d19_relat_1, axiom,
% 4.72/4.92    (![A:$i,B:$i]:
% 4.72/4.92     ( ( v1_relat_1 @ B ) =>
% 4.72/4.92       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 4.72/4.92  thf('32', plain,
% 4.72/4.92      (![X5 : $i, X6 : $i]:
% 4.72/4.92         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 4.72/4.92          | (v5_relat_1 @ X5 @ X6)
% 4.72/4.92          | ~ (v1_relat_1 @ X5))),
% 4.72/4.92      inference('cnf', [status(esa)], [d19_relat_1])).
% 4.72/4.92  thf('33', plain,
% 4.72/4.92      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 4.72/4.92      inference('sup-', [status(thm)], ['31', '32'])).
% 4.72/4.92  thf('34', plain,
% 4.72/4.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf(cc2_relat_1, axiom,
% 4.72/4.92    (![A:$i]:
% 4.72/4.92     ( ( v1_relat_1 @ A ) =>
% 4.72/4.92       ( ![B:$i]:
% 4.72/4.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.72/4.92  thf('35', plain,
% 4.72/4.92      (![X3 : $i, X4 : $i]:
% 4.72/4.92         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 4.72/4.92          | (v1_relat_1 @ X3)
% 4.72/4.92          | ~ (v1_relat_1 @ X4))),
% 4.72/4.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.72/4.92  thf('36', plain,
% 4.72/4.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D))),
% 4.72/4.92      inference('sup-', [status(thm)], ['34', '35'])).
% 4.72/4.92  thf(fc6_relat_1, axiom,
% 4.72/4.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.72/4.92  thf('37', plain,
% 4.72/4.92      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 4.72/4.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.72/4.92  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 4.72/4.92      inference('demod', [status(thm)], ['36', '37'])).
% 4.72/4.92  thf('39', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 4.72/4.92      inference('demod', [status(thm)], ['33', '38'])).
% 4.72/4.92  thf('40', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf(t2_subset, axiom,
% 4.72/4.92    (![A:$i,B:$i]:
% 4.72/4.92     ( ( m1_subset_1 @ A @ B ) =>
% 4.72/4.92       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 4.72/4.92  thf('41', plain,
% 4.72/4.92      (![X1 : $i, X2 : $i]:
% 4.72/4.92         ((r2_hidden @ X1 @ X2)
% 4.72/4.92          | (v1_xboole_0 @ X2)
% 4.72/4.92          | ~ (m1_subset_1 @ X1 @ X2))),
% 4.72/4.92      inference('cnf', [status(esa)], [t2_subset])).
% 4.72/4.92  thf('42', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 4.72/4.92      inference('sup-', [status(thm)], ['40', '41'])).
% 4.72/4.92  thf(l13_xboole_0, axiom,
% 4.72/4.92    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.72/4.92  thf('43', plain,
% 4.72/4.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.72/4.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.72/4.92  thf('44', plain,
% 4.72/4.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.72/4.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.72/4.92  thf('45', plain,
% 4.72/4.92      (![X0 : $i, X1 : $i]:
% 4.72/4.92         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 4.72/4.92      inference('sup+', [status(thm)], ['43', '44'])).
% 4.72/4.92  thf('46', plain, (((sk_B) != (k1_xboole_0))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('47', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (((X0) != (k1_xboole_0))
% 4.72/4.92          | ~ (v1_xboole_0 @ X0)
% 4.72/4.92          | ~ (v1_xboole_0 @ sk_B))),
% 4.72/4.92      inference('sup-', [status(thm)], ['45', '46'])).
% 4.72/4.92  thf('48', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.72/4.92      inference('simplify', [status(thm)], ['47'])).
% 4.72/4.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.72/4.92  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.72/4.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.72/4.92  thf('50', plain, (~ (v1_xboole_0 @ sk_B)),
% 4.72/4.92      inference('simplify_reflect+', [status(thm)], ['48', '49'])).
% 4.72/4.92  thf('51', plain, ((r2_hidden @ sk_F @ sk_B)),
% 4.72/4.92      inference('clc', [status(thm)], ['42', '50'])).
% 4.72/4.92  thf('52', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf(d1_funct_2, axiom,
% 4.72/4.92    (![A:$i,B:$i,C:$i]:
% 4.72/4.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.72/4.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.72/4.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.72/4.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.72/4.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.72/4.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.72/4.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.72/4.92  thf(zf_stmt_1, axiom,
% 4.72/4.92    (![C:$i,B:$i,A:$i]:
% 4.72/4.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.72/4.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.72/4.92  thf('53', plain,
% 4.72/4.92      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.72/4.92         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 4.72/4.92          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 4.72/4.92          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.72/4.92  thf('54', plain,
% 4.72/4.92      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 4.72/4.92        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 4.72/4.92      inference('sup-', [status(thm)], ['52', '53'])).
% 4.72/4.92  thf('55', plain,
% 4.72/4.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('56', plain,
% 4.72/4.92      (![X17 : $i, X18 : $i, X19 : $i]:
% 4.72/4.92         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 4.72/4.92          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 4.72/4.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.72/4.92  thf('57', plain,
% 4.72/4.92      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 4.72/4.92      inference('sup-', [status(thm)], ['55', '56'])).
% 4.72/4.92  thf('58', plain,
% 4.72/4.92      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 4.72/4.92      inference('demod', [status(thm)], ['54', '57'])).
% 4.72/4.92  thf('59', plain,
% 4.72/4.92      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.72/4.92  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 4.72/4.92  thf(zf_stmt_4, axiom,
% 4.72/4.92    (![B:$i,A:$i]:
% 4.72/4.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.72/4.92       ( zip_tseitin_0 @ B @ A ) ))).
% 4.72/4.92  thf(zf_stmt_5, axiom,
% 4.72/4.92    (![A:$i,B:$i,C:$i]:
% 4.72/4.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.72/4.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.72/4.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.72/4.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.72/4.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.72/4.92  thf('60', plain,
% 4.72/4.92      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.72/4.92         (~ (zip_tseitin_0 @ X28 @ X29)
% 4.72/4.92          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 4.72/4.92          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.72/4.92  thf('61', plain,
% 4.72/4.92      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 4.72/4.92      inference('sup-', [status(thm)], ['59', '60'])).
% 4.72/4.92  thf('62', plain,
% 4.72/4.92      (![X23 : $i, X24 : $i]:
% 4.72/4.92         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.72/4.92  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.72/4.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.72/4.92  thf('64', plain,
% 4.72/4.92      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 4.72/4.92      inference('sup+', [status(thm)], ['62', '63'])).
% 4.72/4.92  thf('65', plain, (~ (v1_xboole_0 @ sk_C)),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('66', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 4.72/4.92      inference('sup-', [status(thm)], ['64', '65'])).
% 4.72/4.92  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 4.72/4.92      inference('demod', [status(thm)], ['61', '66'])).
% 4.72/4.92  thf('68', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 4.72/4.92      inference('demod', [status(thm)], ['58', '67'])).
% 4.72/4.92  thf(t12_funct_1, axiom,
% 4.72/4.92    (![A:$i,B:$i]:
% 4.72/4.92     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 4.72/4.92       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 4.72/4.92         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 4.72/4.92  thf('69', plain,
% 4.72/4.92      (![X12 : $i, X13 : $i]:
% 4.72/4.92         (~ (r2_hidden @ X12 @ (k1_relat_1 @ X13))
% 4.72/4.92          | (r2_hidden @ (k1_funct_1 @ X13 @ X12) @ (k2_relat_1 @ X13))
% 4.72/4.92          | ~ (v1_funct_1 @ X13)
% 4.72/4.92          | ~ (v1_relat_1 @ X13))),
% 4.72/4.92      inference('cnf', [status(esa)], [t12_funct_1])).
% 4.72/4.92  thf('70', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (r2_hidden @ X0 @ sk_B)
% 4.72/4.92          | ~ (v1_relat_1 @ sk_D)
% 4.72/4.92          | ~ (v1_funct_1 @ sk_D)
% 4.72/4.92          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 4.72/4.92      inference('sup-', [status(thm)], ['68', '69'])).
% 4.72/4.92  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 4.72/4.92      inference('demod', [status(thm)], ['36', '37'])).
% 4.72/4.92  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('73', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (r2_hidden @ X0 @ sk_B)
% 4.72/4.92          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 4.72/4.92      inference('demod', [status(thm)], ['70', '71', '72'])).
% 4.72/4.92  thf('74', plain,
% 4.72/4.92      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))),
% 4.72/4.92      inference('sup-', [status(thm)], ['51', '73'])).
% 4.72/4.92  thf(t202_relat_1, axiom,
% 4.72/4.92    (![A:$i,B:$i]:
% 4.72/4.92     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 4.72/4.92       ( ![C:$i]:
% 4.72/4.92         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 4.72/4.92  thf('75', plain,
% 4.72/4.92      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.72/4.92         (~ (r2_hidden @ X9 @ (k2_relat_1 @ X10))
% 4.72/4.92          | (r2_hidden @ X9 @ X11)
% 4.72/4.92          | ~ (v5_relat_1 @ X10 @ X11)
% 4.72/4.92          | ~ (v1_relat_1 @ X10))),
% 4.72/4.92      inference('cnf', [status(esa)], [t202_relat_1])).
% 4.72/4.92  thf('76', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (v1_relat_1 @ sk_D)
% 4.72/4.92          | ~ (v5_relat_1 @ sk_D @ X0)
% 4.72/4.92          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ X0))),
% 4.72/4.92      inference('sup-', [status(thm)], ['74', '75'])).
% 4.72/4.92  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 4.72/4.92      inference('demod', [status(thm)], ['36', '37'])).
% 4.72/4.92  thf('78', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (v5_relat_1 @ sk_D @ X0)
% 4.72/4.92          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ X0))),
% 4.72/4.92      inference('demod', [status(thm)], ['76', '77'])).
% 4.72/4.92  thf('79', plain,
% 4.72/4.92      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 4.72/4.92      inference('sup-', [status(thm)], ['39', '78'])).
% 4.72/4.92  thf(d8_partfun1, axiom,
% 4.72/4.92    (![A:$i,B:$i]:
% 4.72/4.92     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 4.72/4.92       ( ![C:$i]:
% 4.72/4.92         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 4.72/4.92           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 4.72/4.92  thf('80', plain,
% 4.72/4.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.72/4.92         (~ (r2_hidden @ X31 @ (k1_relat_1 @ X32))
% 4.72/4.92          | ((k7_partfun1 @ X33 @ X32 @ X31) = (k1_funct_1 @ X32 @ X31))
% 4.72/4.92          | ~ (v1_funct_1 @ X32)
% 4.72/4.92          | ~ (v5_relat_1 @ X32 @ X33)
% 4.72/4.92          | ~ (v1_relat_1 @ X32))),
% 4.72/4.92      inference('cnf', [status(esa)], [d8_partfun1])).
% 4.72/4.92  thf('81', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (v1_relat_1 @ sk_E)
% 4.72/4.92          | ~ (v5_relat_1 @ sk_E @ X0)
% 4.72/4.92          | ~ (v1_funct_1 @ sk_E)
% 4.72/4.92          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 4.72/4.92              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 4.72/4.92      inference('sup-', [status(thm)], ['79', '80'])).
% 4.72/4.92  thf('82', plain,
% 4.72/4.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('83', plain,
% 4.72/4.92      (![X3 : $i, X4 : $i]:
% 4.72/4.92         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 4.72/4.92          | (v1_relat_1 @ X3)
% 4.72/4.92          | ~ (v1_relat_1 @ X4))),
% 4.72/4.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.72/4.92  thf('84', plain,
% 4.72/4.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 4.72/4.92      inference('sup-', [status(thm)], ['82', '83'])).
% 4.72/4.92  thf('85', plain,
% 4.72/4.92      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 4.72/4.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.72/4.92  thf('86', plain, ((v1_relat_1 @ sk_E)),
% 4.72/4.92      inference('demod', [status(thm)], ['84', '85'])).
% 4.72/4.92  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 4.72/4.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.72/4.92  thf('88', plain,
% 4.72/4.92      (![X0 : $i]:
% 4.72/4.92         (~ (v5_relat_1 @ sk_E @ X0)
% 4.72/4.92          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 4.72/4.92              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 4.72/4.92      inference('demod', [status(thm)], ['81', '86', '87'])).
% 4.72/4.92  thf('89', plain,
% 4.72/4.92      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 4.72/4.92         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 4.72/4.92      inference('sup-', [status(thm)], ['30', '88'])).
% 4.72/4.92  thf('90', plain,
% 4.72/4.92      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 4.72/4.92         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 4.72/4.92      inference('demod', [status(thm)], ['27', '89'])).
% 4.72/4.92  thf('91', plain, ($false),
% 4.72/4.92      inference('simplify_reflect-', [status(thm)], ['26', '90'])).
% 4.72/4.92  
% 4.72/4.92  % SZS output end Refutation
% 4.72/4.92  
% 4.72/4.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

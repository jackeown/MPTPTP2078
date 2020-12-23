%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z83pkjxPKX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:09 EST 2020

% Result     : Theorem 7.53s
% Output     : Refutation 7.53s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 218 expanded)
%              Number of leaves         :   46 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          : 1132 (4270 expanded)
%              Number of equality atoms :   58 ( 182 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['45','50'])).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X10 @ X9 ) @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v5_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','73'])).

thf('75',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['42','74'])).

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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X29 @ ( k1_relat_1 @ X30 ) )
      | ( ( k7_partfun1 @ X31 @ X30 @ X29 )
        = ( k1_funct_1 @ X30 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('82',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['77','82','83'])).

thf('85',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','84'])).

thf('86',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z83pkjxPKX
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:51:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.53/7.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.53/7.73  % Solved by: fo/fo7.sh
% 7.53/7.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.53/7.73  % done 4116 iterations in 7.274s
% 7.53/7.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.53/7.73  % SZS output start Refutation
% 7.53/7.73  thf(sk_A_type, type, sk_A: $i).
% 7.53/7.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.53/7.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.53/7.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.53/7.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.53/7.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.53/7.73  thf(sk_F_type, type, sk_F: $i).
% 7.53/7.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.53/7.73  thf(sk_E_type, type, sk_E: $i).
% 7.53/7.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.53/7.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.53/7.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.53/7.73  thf(sk_B_type, type, sk_B: $i).
% 7.53/7.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.53/7.73  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 7.53/7.73  thf(sk_C_type, type, sk_C: $i).
% 7.53/7.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.53/7.73  thf(sk_D_type, type, sk_D: $i).
% 7.53/7.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.53/7.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.53/7.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.53/7.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.53/7.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 7.53/7.73  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 7.53/7.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.53/7.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 7.53/7.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.53/7.73  thf(t186_funct_2, conjecture,
% 7.53/7.73    (![A:$i,B:$i,C:$i]:
% 7.53/7.73     ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.53/7.73       ( ![D:$i]:
% 7.53/7.73         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.53/7.73             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.53/7.73           ( ![E:$i]:
% 7.53/7.73             ( ( ( v1_funct_1 @ E ) & 
% 7.53/7.73                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 7.53/7.73               ( ![F:$i]:
% 7.53/7.73                 ( ( m1_subset_1 @ F @ B ) =>
% 7.53/7.73                   ( ( r1_tarski @
% 7.53/7.73                       ( k2_relset_1 @ B @ C @ D ) @ 
% 7.53/7.73                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 7.53/7.73                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.53/7.73                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 7.53/7.73                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.53/7.73  thf(zf_stmt_0, negated_conjecture,
% 7.53/7.73    (~( ![A:$i,B:$i,C:$i]:
% 7.53/7.73        ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.53/7.73          ( ![D:$i]:
% 7.53/7.73            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.53/7.73                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.53/7.73              ( ![E:$i]:
% 7.53/7.73                ( ( ( v1_funct_1 @ E ) & 
% 7.53/7.73                    ( m1_subset_1 @
% 7.53/7.73                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 7.53/7.73                  ( ![F:$i]:
% 7.53/7.73                    ( ( m1_subset_1 @ F @ B ) =>
% 7.53/7.73                      ( ( r1_tarski @
% 7.53/7.73                          ( k2_relset_1 @ B @ C @ D ) @ 
% 7.53/7.73                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 7.53/7.73                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.53/7.73                          ( ( k1_funct_1 @
% 7.53/7.73                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 7.53/7.73                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 7.53/7.73    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 7.53/7.73  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 7.53/7.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.73  thf('1', plain,
% 7.53/7.73      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.53/7.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.73  thf(redefinition_k1_relset_1, axiom,
% 7.53/7.73    (![A:$i,B:$i,C:$i]:
% 7.53/7.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.53/7.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.53/7.73  thf('2', plain,
% 7.53/7.73      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.53/7.73         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 7.53/7.73          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 7.53/7.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.53/7.74  thf('3', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 7.53/7.74      inference('sup-', [status(thm)], ['1', '2'])).
% 7.53/7.74  thf('4', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf(t185_funct_2, axiom,
% 7.53/7.74    (![A:$i,B:$i,C:$i]:
% 7.53/7.74     ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.53/7.74       ( ![D:$i]:
% 7.53/7.74         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.53/7.74             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.53/7.74           ( ![E:$i]:
% 7.53/7.74             ( ( ( v1_funct_1 @ E ) & 
% 7.53/7.74                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 7.53/7.74               ( ![F:$i]:
% 7.53/7.74                 ( ( m1_subset_1 @ F @ B ) =>
% 7.53/7.74                   ( ( r1_tarski @
% 7.53/7.74                       ( k2_relset_1 @ B @ C @ D ) @ 
% 7.53/7.74                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 7.53/7.74                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 7.53/7.74                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 7.53/7.74                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.53/7.74  thf('5', plain,
% 7.53/7.74      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.53/7.74         (~ (v1_funct_1 @ X32)
% 7.53/7.74          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 7.53/7.74          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 7.53/7.74          | ~ (m1_subset_1 @ X35 @ X33)
% 7.53/7.74          | ((k1_funct_1 @ (k8_funct_2 @ X33 @ X34 @ X37 @ X32 @ X36) @ X35)
% 7.53/7.74              = (k1_funct_1 @ X36 @ (k1_funct_1 @ X32 @ X35)))
% 7.53/7.74          | ((X33) = (k1_xboole_0))
% 7.53/7.74          | ~ (r1_tarski @ (k2_relset_1 @ X33 @ X34 @ X32) @ 
% 7.53/7.74               (k1_relset_1 @ X34 @ X37 @ X36))
% 7.53/7.74          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X37)))
% 7.53/7.74          | ~ (v1_funct_1 @ X36)
% 7.53/7.74          | (v1_xboole_0 @ X34))),
% 7.53/7.74      inference('cnf', [status(esa)], [t185_funct_2])).
% 7.53/7.74  thf('6', plain,
% 7.53/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.53/7.74         ((v1_xboole_0 @ sk_C)
% 7.53/7.74          | ~ (v1_funct_1 @ X0)
% 7.53/7.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 7.53/7.74          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 7.53/7.74               (k1_relset_1 @ sk_C @ X1 @ X0))
% 7.53/7.74          | ((sk_B) = (k1_xboole_0))
% 7.53/7.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 7.53/7.74              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.53/7.74          | ~ (m1_subset_1 @ X2 @ sk_B)
% 7.53/7.74          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 7.53/7.74          | ~ (v1_funct_1 @ sk_D))),
% 7.53/7.74      inference('sup-', [status(thm)], ['4', '5'])).
% 7.53/7.74  thf('7', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf(redefinition_k2_relset_1, axiom,
% 7.53/7.74    (![A:$i,B:$i,C:$i]:
% 7.53/7.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.53/7.74       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.53/7.74  thf('8', plain,
% 7.53/7.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.53/7.74         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 7.53/7.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 7.53/7.74      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.53/7.74  thf('9', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 7.53/7.74      inference('sup-', [status(thm)], ['7', '8'])).
% 7.53/7.74  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('12', plain,
% 7.53/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.53/7.74         ((v1_xboole_0 @ sk_C)
% 7.53/7.74          | ~ (v1_funct_1 @ X0)
% 7.53/7.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 7.53/7.74          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 7.53/7.74          | ((sk_B) = (k1_xboole_0))
% 7.53/7.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 7.53/7.74              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.53/7.74          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 7.53/7.74      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 7.53/7.74  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('14', plain,
% 7.53/7.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.53/7.74         ((v1_xboole_0 @ sk_C)
% 7.53/7.74          | ~ (v1_funct_1 @ X0)
% 7.53/7.74          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 7.53/7.74          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 7.53/7.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 7.53/7.74              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 7.53/7.74          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 7.53/7.74      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 7.53/7.74  thf('15', plain,
% 7.53/7.74      (![X0 : $i]:
% 7.53/7.74         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 7.53/7.74          | ~ (m1_subset_1 @ X0 @ sk_B)
% 7.53/7.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 7.53/7.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.53/7.74          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 7.53/7.74          | ~ (v1_funct_1 @ sk_E)
% 7.53/7.74          | (v1_xboole_0 @ sk_C))),
% 7.53/7.74      inference('sup-', [status(thm)], ['3', '14'])).
% 7.53/7.74  thf('16', plain,
% 7.53/7.74      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 7.53/7.74        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('17', plain,
% 7.53/7.74      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 7.53/7.74      inference('sup-', [status(thm)], ['1', '2'])).
% 7.53/7.74  thf('18', plain,
% 7.53/7.74      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 7.53/7.74      inference('demod', [status(thm)], ['16', '17'])).
% 7.53/7.74  thf('19', plain,
% 7.53/7.74      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 7.53/7.74      inference('sup-', [status(thm)], ['7', '8'])).
% 7.53/7.74  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 7.53/7.74      inference('demod', [status(thm)], ['18', '19'])).
% 7.53/7.74  thf('21', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('23', plain,
% 7.53/7.74      (![X0 : $i]:
% 7.53/7.74         (~ (m1_subset_1 @ X0 @ sk_B)
% 7.53/7.74          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 7.53/7.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.53/7.74          | (v1_xboole_0 @ sk_C))),
% 7.53/7.74      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 7.53/7.74  thf('24', plain, (~ (v1_xboole_0 @ sk_C)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('25', plain,
% 7.53/7.74      (![X0 : $i]:
% 7.53/7.74         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 7.53/7.74            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 7.53/7.74          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 7.53/7.74      inference('clc', [status(thm)], ['23', '24'])).
% 7.53/7.74  thf('26', plain,
% 7.53/7.74      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 7.53/7.74         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.53/7.74      inference('sup-', [status(thm)], ['0', '25'])).
% 7.53/7.74  thf('27', plain,
% 7.53/7.74      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 7.53/7.74         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('28', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf(cc2_relset_1, axiom,
% 7.53/7.74    (![A:$i,B:$i,C:$i]:
% 7.53/7.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.53/7.74       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 7.53/7.74  thf('29', plain,
% 7.53/7.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.53/7.74         ((v5_relat_1 @ X12 @ X14)
% 7.53/7.74          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 7.53/7.74      inference('cnf', [status(esa)], [cc2_relset_1])).
% 7.53/7.74  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 7.53/7.74      inference('sup-', [status(thm)], ['28', '29'])).
% 7.53/7.74  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf(t2_subset, axiom,
% 7.53/7.74    (![A:$i,B:$i]:
% 7.53/7.74     ( ( m1_subset_1 @ A @ B ) =>
% 7.53/7.74       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 7.53/7.74  thf('32', plain,
% 7.53/7.74      (![X1 : $i, X2 : $i]:
% 7.53/7.74         ((r2_hidden @ X1 @ X2)
% 7.53/7.74          | (v1_xboole_0 @ X2)
% 7.53/7.74          | ~ (m1_subset_1 @ X1 @ X2))),
% 7.53/7.74      inference('cnf', [status(esa)], [t2_subset])).
% 7.53/7.74  thf('33', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 7.53/7.74      inference('sup-', [status(thm)], ['31', '32'])).
% 7.53/7.74  thf(l13_xboole_0, axiom,
% 7.53/7.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 7.53/7.74  thf('34', plain,
% 7.53/7.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.53/7.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.53/7.74  thf('35', plain,
% 7.53/7.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 7.53/7.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 7.53/7.74  thf('36', plain,
% 7.53/7.74      (![X0 : $i, X1 : $i]:
% 7.53/7.74         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 7.53/7.74      inference('sup+', [status(thm)], ['34', '35'])).
% 7.53/7.74  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('38', plain,
% 7.53/7.74      (![X0 : $i]:
% 7.53/7.74         (((X0) != (k1_xboole_0))
% 7.53/7.74          | ~ (v1_xboole_0 @ X0)
% 7.53/7.74          | ~ (v1_xboole_0 @ sk_B))),
% 7.53/7.74      inference('sup-', [status(thm)], ['36', '37'])).
% 7.53/7.74  thf('39', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 7.53/7.74      inference('simplify', [status(thm)], ['38'])).
% 7.53/7.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 7.53/7.74  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.53/7.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.53/7.74  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 7.53/7.74      inference('simplify_reflect+', [status(thm)], ['39', '40'])).
% 7.53/7.74  thf('42', plain, ((r2_hidden @ sk_F @ sk_B)),
% 7.53/7.74      inference('clc', [status(thm)], ['33', '41'])).
% 7.53/7.74  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 7.53/7.74      inference('demod', [status(thm)], ['18', '19'])).
% 7.53/7.74  thf(d19_relat_1, axiom,
% 7.53/7.74    (![A:$i,B:$i]:
% 7.53/7.74     ( ( v1_relat_1 @ B ) =>
% 7.53/7.74       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 7.53/7.74  thf('44', plain,
% 7.53/7.74      (![X5 : $i, X6 : $i]:
% 7.53/7.74         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 7.53/7.74          | (v5_relat_1 @ X5 @ X6)
% 7.53/7.74          | ~ (v1_relat_1 @ X5))),
% 7.53/7.74      inference('cnf', [status(esa)], [d19_relat_1])).
% 7.53/7.74  thf('45', plain,
% 7.53/7.74      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 7.53/7.74      inference('sup-', [status(thm)], ['43', '44'])).
% 7.53/7.74  thf('46', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf(cc2_relat_1, axiom,
% 7.53/7.74    (![A:$i]:
% 7.53/7.74     ( ( v1_relat_1 @ A ) =>
% 7.53/7.74       ( ![B:$i]:
% 7.53/7.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 7.53/7.74  thf('47', plain,
% 7.53/7.74      (![X3 : $i, X4 : $i]:
% 7.53/7.74         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 7.53/7.74          | (v1_relat_1 @ X3)
% 7.53/7.74          | ~ (v1_relat_1 @ X4))),
% 7.53/7.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.53/7.74  thf('48', plain,
% 7.53/7.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D))),
% 7.53/7.74      inference('sup-', [status(thm)], ['46', '47'])).
% 7.53/7.74  thf(fc6_relat_1, axiom,
% 7.53/7.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 7.53/7.74  thf('49', plain,
% 7.53/7.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 7.53/7.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.53/7.74  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 7.53/7.74      inference('demod', [status(thm)], ['48', '49'])).
% 7.53/7.74  thf('51', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 7.53/7.74      inference('demod', [status(thm)], ['45', '50'])).
% 7.53/7.74  thf('52', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf(d1_funct_2, axiom,
% 7.53/7.74    (![A:$i,B:$i,C:$i]:
% 7.53/7.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.53/7.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.53/7.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.53/7.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.53/7.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.53/7.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.53/7.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.53/7.74  thf(zf_stmt_1, axiom,
% 7.53/7.74    (![C:$i,B:$i,A:$i]:
% 7.53/7.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.53/7.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.53/7.74  thf('53', plain,
% 7.53/7.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 7.53/7.74         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 7.53/7.74          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 7.53/7.74          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.53/7.74  thf('54', plain,
% 7.53/7.74      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 7.53/7.74        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 7.53/7.74      inference('sup-', [status(thm)], ['52', '53'])).
% 7.53/7.74  thf('55', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('56', plain,
% 7.53/7.74      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.53/7.74         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 7.53/7.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 7.53/7.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.53/7.74  thf('57', plain,
% 7.53/7.74      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 7.53/7.74      inference('sup-', [status(thm)], ['55', '56'])).
% 7.53/7.74  thf('58', plain,
% 7.53/7.74      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 7.53/7.74      inference('demod', [status(thm)], ['54', '57'])).
% 7.53/7.74  thf('59', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.53/7.74  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 7.53/7.74  thf(zf_stmt_4, axiom,
% 7.53/7.74    (![B:$i,A:$i]:
% 7.53/7.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.53/7.74       ( zip_tseitin_0 @ B @ A ) ))).
% 7.53/7.74  thf(zf_stmt_5, axiom,
% 7.53/7.74    (![A:$i,B:$i,C:$i]:
% 7.53/7.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.53/7.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.53/7.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.53/7.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.53/7.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.53/7.74  thf('60', plain,
% 7.53/7.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 7.53/7.74         (~ (zip_tseitin_0 @ X26 @ X27)
% 7.53/7.74          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 7.53/7.74          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.53/7.74  thf('61', plain,
% 7.53/7.74      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 7.53/7.74      inference('sup-', [status(thm)], ['59', '60'])).
% 7.53/7.74  thf('62', plain,
% 7.53/7.74      (![X21 : $i, X22 : $i]:
% 7.53/7.74         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_4])).
% 7.53/7.74  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 7.53/7.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 7.53/7.74  thf('64', plain,
% 7.53/7.74      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 7.53/7.74      inference('sup+', [status(thm)], ['62', '63'])).
% 7.53/7.74  thf('65', plain, (~ (v1_xboole_0 @ sk_C)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('66', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 7.53/7.74      inference('sup-', [status(thm)], ['64', '65'])).
% 7.53/7.74  thf('67', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 7.53/7.74      inference('demod', [status(thm)], ['61', '66'])).
% 7.53/7.74  thf('68', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 7.53/7.74      inference('demod', [status(thm)], ['58', '67'])).
% 7.53/7.74  thf(t172_funct_1, axiom,
% 7.53/7.74    (![A:$i,B:$i]:
% 7.53/7.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 7.53/7.74       ( ![C:$i]:
% 7.53/7.74         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 7.53/7.74           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 7.53/7.74  thf('69', plain,
% 7.53/7.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 7.53/7.74         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 7.53/7.74          | (r2_hidden @ (k1_funct_1 @ X10 @ X9) @ X11)
% 7.53/7.74          | ~ (v1_funct_1 @ X10)
% 7.53/7.74          | ~ (v5_relat_1 @ X10 @ X11)
% 7.53/7.74          | ~ (v1_relat_1 @ X10))),
% 7.53/7.74      inference('cnf', [status(esa)], [t172_funct_1])).
% 7.53/7.74  thf('70', plain,
% 7.53/7.74      (![X0 : $i, X1 : $i]:
% 7.53/7.74         (~ (r2_hidden @ X0 @ sk_B)
% 7.53/7.74          | ~ (v1_relat_1 @ sk_D)
% 7.53/7.74          | ~ (v5_relat_1 @ sk_D @ X1)
% 7.53/7.74          | ~ (v1_funct_1 @ sk_D)
% 7.53/7.74          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 7.53/7.74      inference('sup-', [status(thm)], ['68', '69'])).
% 7.53/7.74  thf('71', plain, ((v1_relat_1 @ sk_D)),
% 7.53/7.74      inference('demod', [status(thm)], ['48', '49'])).
% 7.53/7.74  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('73', plain,
% 7.53/7.74      (![X0 : $i, X1 : $i]:
% 7.53/7.74         (~ (r2_hidden @ X0 @ sk_B)
% 7.53/7.74          | ~ (v5_relat_1 @ sk_D @ X1)
% 7.53/7.74          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 7.53/7.74      inference('demod', [status(thm)], ['70', '71', '72'])).
% 7.53/7.74  thf('74', plain,
% 7.53/7.74      (![X0 : $i]:
% 7.53/7.74         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 7.53/7.74          | ~ (r2_hidden @ X0 @ sk_B))),
% 7.53/7.74      inference('sup-', [status(thm)], ['51', '73'])).
% 7.53/7.74  thf('75', plain,
% 7.53/7.74      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 7.53/7.74      inference('sup-', [status(thm)], ['42', '74'])).
% 7.53/7.74  thf(d8_partfun1, axiom,
% 7.53/7.74    (![A:$i,B:$i]:
% 7.53/7.74     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 7.53/7.74       ( ![C:$i]:
% 7.53/7.74         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 7.53/7.74           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 7.53/7.74  thf('76', plain,
% 7.53/7.74      (![X29 : $i, X30 : $i, X31 : $i]:
% 7.53/7.74         (~ (r2_hidden @ X29 @ (k1_relat_1 @ X30))
% 7.53/7.74          | ((k7_partfun1 @ X31 @ X30 @ X29) = (k1_funct_1 @ X30 @ X29))
% 7.53/7.74          | ~ (v1_funct_1 @ X30)
% 7.53/7.74          | ~ (v5_relat_1 @ X30 @ X31)
% 7.53/7.74          | ~ (v1_relat_1 @ X30))),
% 7.53/7.74      inference('cnf', [status(esa)], [d8_partfun1])).
% 7.53/7.74  thf('77', plain,
% 7.53/7.74      (![X0 : $i]:
% 7.53/7.74         (~ (v1_relat_1 @ sk_E)
% 7.53/7.74          | ~ (v5_relat_1 @ sk_E @ X0)
% 7.53/7.74          | ~ (v1_funct_1 @ sk_E)
% 7.53/7.74          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.53/7.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 7.53/7.74      inference('sup-', [status(thm)], ['75', '76'])).
% 7.53/7.74  thf('78', plain,
% 7.53/7.74      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('79', plain,
% 7.53/7.74      (![X3 : $i, X4 : $i]:
% 7.53/7.74         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 7.53/7.74          | (v1_relat_1 @ X3)
% 7.53/7.74          | ~ (v1_relat_1 @ X4))),
% 7.53/7.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 7.53/7.74  thf('80', plain,
% 7.53/7.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 7.53/7.74      inference('sup-', [status(thm)], ['78', '79'])).
% 7.53/7.74  thf('81', plain,
% 7.53/7.74      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 7.53/7.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 7.53/7.74  thf('82', plain, ((v1_relat_1 @ sk_E)),
% 7.53/7.74      inference('demod', [status(thm)], ['80', '81'])).
% 7.53/7.74  thf('83', plain, ((v1_funct_1 @ sk_E)),
% 7.53/7.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.53/7.74  thf('84', plain,
% 7.53/7.74      (![X0 : $i]:
% 7.53/7.74         (~ (v5_relat_1 @ sk_E @ X0)
% 7.53/7.74          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.53/7.74              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 7.53/7.74      inference('demod', [status(thm)], ['77', '82', '83'])).
% 7.53/7.74  thf('85', plain,
% 7.53/7.74      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 7.53/7.74         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.53/7.74      inference('sup-', [status(thm)], ['30', '84'])).
% 7.53/7.74  thf('86', plain,
% 7.53/7.74      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 7.53/7.74         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 7.53/7.74      inference('demod', [status(thm)], ['27', '85'])).
% 7.53/7.74  thf('87', plain, ($false),
% 7.53/7.74      inference('simplify_reflect-', [status(thm)], ['26', '86'])).
% 7.53/7.74  
% 7.53/7.74  % SZS output end Refutation
% 7.53/7.74  
% 7.53/7.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

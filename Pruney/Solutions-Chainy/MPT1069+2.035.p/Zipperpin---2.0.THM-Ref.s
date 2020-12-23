%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a9sO4Nfd3z

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:05 EST 2020

% Result     : Theorem 6.82s
% Output     : Refutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 209 expanded)
%              Number of leaves         :   45 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          : 1108 (4228 expanded)
%              Number of equality atoms :   58 ( 182 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ X32 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X32 @ X33 @ X36 @ X31 @ X35 ) @ X34 )
        = ( k1_funct_1 @ X35 @ ( k1_funct_1 @ X31 @ X34 ) ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X32 @ X33 @ X31 ) @ ( k1_relset_1 @ X33 @ X36 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X33 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ( X22
        = ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['56','65'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X6 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X6 @ X5 ) @ X7 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v5_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['46','47'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','71'])).

thf('73',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['42','72'])).

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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k7_partfun1 @ X30 @ X29 @ X28 )
        = ( k1_funct_1 @ X29 @ X28 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['75','78','79'])).

thf('81',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','80'])).

thf('82',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a9sO4Nfd3z
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:54:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.82/6.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.82/6.99  % Solved by: fo/fo7.sh
% 6.82/6.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.82/6.99  % done 4211 iterations in 6.537s
% 6.82/6.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.82/6.99  % SZS output start Refutation
% 6.82/6.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.82/6.99  thf(sk_D_type, type, sk_D: $i).
% 6.82/6.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.82/6.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.82/6.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.82/6.99  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 6.82/6.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.82/6.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.82/6.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.82/6.99  thf(sk_E_type, type, sk_E: $i).
% 6.82/6.99  thf(sk_A_type, type, sk_A: $i).
% 6.82/6.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.82/6.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.82/6.99  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 6.82/6.99  thf(sk_F_type, type, sk_F: $i).
% 6.82/6.99  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 6.82/6.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.82/6.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 6.82/6.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.82/6.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.82/6.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.82/6.99  thf(sk_B_type, type, sk_B: $i).
% 6.82/6.99  thf(sk_C_type, type, sk_C: $i).
% 6.82/6.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.82/6.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 6.82/6.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.82/6.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.82/6.99  thf(t186_funct_2, conjecture,
% 6.82/6.99    (![A:$i,B:$i,C:$i]:
% 6.82/6.99     ( ( ~( v1_xboole_0 @ C ) ) =>
% 6.82/6.99       ( ![D:$i]:
% 6.82/6.99         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 6.82/6.99             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.82/6.99           ( ![E:$i]:
% 6.82/6.99             ( ( ( v1_funct_1 @ E ) & 
% 6.82/6.99                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 6.82/6.99               ( ![F:$i]:
% 6.82/6.99                 ( ( m1_subset_1 @ F @ B ) =>
% 6.82/6.99                   ( ( r1_tarski @
% 6.82/6.99                       ( k2_relset_1 @ B @ C @ D ) @ 
% 6.82/6.99                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 6.82/6.99                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.82/6.99                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 6.82/6.99                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.82/6.99  thf(zf_stmt_0, negated_conjecture,
% 6.82/6.99    (~( ![A:$i,B:$i,C:$i]:
% 6.82/6.99        ( ( ~( v1_xboole_0 @ C ) ) =>
% 6.82/6.99          ( ![D:$i]:
% 6.82/6.99            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 6.82/6.99                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.82/6.99              ( ![E:$i]:
% 6.82/6.99                ( ( ( v1_funct_1 @ E ) & 
% 6.82/6.99                    ( m1_subset_1 @
% 6.82/6.99                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 6.82/6.99                  ( ![F:$i]:
% 6.82/6.99                    ( ( m1_subset_1 @ F @ B ) =>
% 6.82/6.99                      ( ( r1_tarski @
% 6.82/6.99                          ( k2_relset_1 @ B @ C @ D ) @ 
% 6.82/6.99                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 6.82/6.99                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.82/6.99                          ( ( k1_funct_1 @
% 6.82/6.99                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 6.82/6.99                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 6.82/6.99    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 6.82/6.99  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 6.82/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/6.99  thf('1', plain,
% 6.82/6.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 6.82/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/6.99  thf(redefinition_k1_relset_1, axiom,
% 6.82/6.99    (![A:$i,B:$i,C:$i]:
% 6.82/6.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.82/6.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.82/6.99  thf('2', plain,
% 6.82/6.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.82/6.99         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 6.82/6.99          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.82/6.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.82/6.99  thf('3', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 6.82/6.99      inference('sup-', [status(thm)], ['1', '2'])).
% 6.82/6.99  thf('4', plain,
% 6.82/6.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.82/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/6.99  thf(t185_funct_2, axiom,
% 6.82/6.99    (![A:$i,B:$i,C:$i]:
% 6.82/6.99     ( ( ~( v1_xboole_0 @ C ) ) =>
% 6.82/6.99       ( ![D:$i]:
% 6.82/6.99         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 6.82/6.99             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 6.82/6.99           ( ![E:$i]:
% 6.82/6.99             ( ( ( v1_funct_1 @ E ) & 
% 6.82/6.99                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 6.82/6.99               ( ![F:$i]:
% 6.82/6.99                 ( ( m1_subset_1 @ F @ B ) =>
% 6.82/6.99                   ( ( r1_tarski @
% 6.82/6.99                       ( k2_relset_1 @ B @ C @ D ) @ 
% 6.82/6.99                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 6.82/6.99                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 6.82/6.99                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 6.82/6.99                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.82/6.99  thf('5', plain,
% 6.82/6.99      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 6.82/6.99         (~ (v1_funct_1 @ X31)
% 6.82/6.99          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 6.82/6.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 6.82/6.99          | ~ (m1_subset_1 @ X34 @ X32)
% 6.82/6.99          | ((k1_funct_1 @ (k8_funct_2 @ X32 @ X33 @ X36 @ X31 @ X35) @ X34)
% 6.82/6.99              = (k1_funct_1 @ X35 @ (k1_funct_1 @ X31 @ X34)))
% 6.82/6.99          | ((X32) = (k1_xboole_0))
% 6.82/6.99          | ~ (r1_tarski @ (k2_relset_1 @ X32 @ X33 @ X31) @ 
% 6.82/6.99               (k1_relset_1 @ X33 @ X36 @ X35))
% 6.82/6.99          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X36)))
% 6.82/6.99          | ~ (v1_funct_1 @ X35)
% 6.82/6.99          | (v1_xboole_0 @ X33))),
% 6.82/6.99      inference('cnf', [status(esa)], [t185_funct_2])).
% 6.82/6.99  thf('6', plain,
% 6.82/6.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.82/6.99         ((v1_xboole_0 @ sk_C)
% 6.82/6.99          | ~ (v1_funct_1 @ X0)
% 6.82/6.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 6.82/6.99          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 6.82/6.99               (k1_relset_1 @ sk_C @ X1 @ X0))
% 6.82/6.99          | ((sk_B) = (k1_xboole_0))
% 6.82/6.99          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 6.82/6.99              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 6.82/6.99          | ~ (m1_subset_1 @ X2 @ sk_B)
% 6.82/6.99          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 6.82/6.99          | ~ (v1_funct_1 @ sk_D))),
% 6.82/6.99      inference('sup-', [status(thm)], ['4', '5'])).
% 6.82/6.99  thf('7', plain,
% 6.82/6.99      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.82/6.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/6.99  thf(redefinition_k2_relset_1, axiom,
% 6.82/6.99    (![A:$i,B:$i,C:$i]:
% 6.82/6.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.82/6.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.82/6.99  thf('8', plain,
% 6.82/6.99      (![X17 : $i, X18 : $i, X19 : $i]:
% 6.82/6.99         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 6.82/6.99          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 6.82/6.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.82/7.00  thf('9', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.82/7.00      inference('sup-', [status(thm)], ['7', '8'])).
% 6.82/7.00  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('12', plain,
% 6.82/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.82/7.00         ((v1_xboole_0 @ sk_C)
% 6.82/7.00          | ~ (v1_funct_1 @ X0)
% 6.82/7.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 6.82/7.00          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 6.82/7.00          | ((sk_B) = (k1_xboole_0))
% 6.82/7.00          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 6.82/7.00              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 6.82/7.00          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 6.82/7.00      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 6.82/7.00  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('14', plain,
% 6.82/7.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.82/7.00         ((v1_xboole_0 @ sk_C)
% 6.82/7.00          | ~ (v1_funct_1 @ X0)
% 6.82/7.00          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 6.82/7.00          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 6.82/7.00          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 6.82/7.00              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 6.82/7.00          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 6.82/7.00      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 6.82/7.00  thf('15', plain,
% 6.82/7.00      (![X0 : $i]:
% 6.82/7.00         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 6.82/7.00          | ~ (m1_subset_1 @ X0 @ sk_B)
% 6.82/7.00          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 6.82/7.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 6.82/7.00          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 6.82/7.00          | ~ (v1_funct_1 @ sk_E)
% 6.82/7.00          | (v1_xboole_0 @ sk_C))),
% 6.82/7.00      inference('sup-', [status(thm)], ['3', '14'])).
% 6.82/7.00  thf('16', plain,
% 6.82/7.00      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 6.82/7.00        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('17', plain,
% 6.82/7.00      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 6.82/7.00      inference('sup-', [status(thm)], ['1', '2'])).
% 6.82/7.00  thf('18', plain,
% 6.82/7.00      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 6.82/7.00      inference('demod', [status(thm)], ['16', '17'])).
% 6.82/7.00  thf('19', plain,
% 6.82/7.00      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 6.82/7.00      inference('sup-', [status(thm)], ['7', '8'])).
% 6.82/7.00  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 6.82/7.00      inference('demod', [status(thm)], ['18', '19'])).
% 6.82/7.00  thf('21', plain,
% 6.82/7.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('23', plain,
% 6.82/7.00      (![X0 : $i]:
% 6.82/7.00         (~ (m1_subset_1 @ X0 @ sk_B)
% 6.82/7.00          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 6.82/7.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 6.82/7.00          | (v1_xboole_0 @ sk_C))),
% 6.82/7.00      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 6.82/7.00  thf('24', plain, (~ (v1_xboole_0 @ sk_C)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('25', plain,
% 6.82/7.00      (![X0 : $i]:
% 6.82/7.00         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 6.82/7.00            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 6.82/7.00          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 6.82/7.00      inference('clc', [status(thm)], ['23', '24'])).
% 6.82/7.00  thf('26', plain,
% 6.82/7.00      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 6.82/7.00         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 6.82/7.00      inference('sup-', [status(thm)], ['0', '25'])).
% 6.82/7.00  thf('27', plain,
% 6.82/7.00      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 6.82/7.00         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('28', plain,
% 6.82/7.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf(cc2_relset_1, axiom,
% 6.82/7.00    (![A:$i,B:$i,C:$i]:
% 6.82/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.82/7.00       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 6.82/7.00  thf('29', plain,
% 6.82/7.00      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.82/7.00         ((v5_relat_1 @ X11 @ X13)
% 6.82/7.00          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 6.82/7.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 6.82/7.00  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 6.82/7.00      inference('sup-', [status(thm)], ['28', '29'])).
% 6.82/7.00  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf(t2_subset, axiom,
% 6.82/7.00    (![A:$i,B:$i]:
% 6.82/7.00     ( ( m1_subset_1 @ A @ B ) =>
% 6.82/7.00       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 6.82/7.00  thf('32', plain,
% 6.82/7.00      (![X1 : $i, X2 : $i]:
% 6.82/7.00         ((r2_hidden @ X1 @ X2)
% 6.82/7.00          | (v1_xboole_0 @ X2)
% 6.82/7.00          | ~ (m1_subset_1 @ X1 @ X2))),
% 6.82/7.00      inference('cnf', [status(esa)], [t2_subset])).
% 6.82/7.00  thf('33', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 6.82/7.00      inference('sup-', [status(thm)], ['31', '32'])).
% 6.82/7.00  thf(l13_xboole_0, axiom,
% 6.82/7.00    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.82/7.00  thf('34', plain,
% 6.82/7.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.82/7.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.82/7.00  thf('35', plain,
% 6.82/7.00      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.82/7.00      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.82/7.00  thf('36', plain,
% 6.82/7.00      (![X0 : $i, X1 : $i]:
% 6.82/7.00         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 6.82/7.00      inference('sup+', [status(thm)], ['34', '35'])).
% 6.82/7.00  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('38', plain,
% 6.82/7.00      (![X0 : $i]:
% 6.82/7.00         (((X0) != (k1_xboole_0))
% 6.82/7.00          | ~ (v1_xboole_0 @ X0)
% 6.82/7.00          | ~ (v1_xboole_0 @ sk_B))),
% 6.82/7.00      inference('sup-', [status(thm)], ['36', '37'])).
% 6.82/7.00  thf('39', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.82/7.00      inference('simplify', [status(thm)], ['38'])).
% 6.82/7.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.82/7.00  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.82/7.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.82/7.00  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 6.82/7.00      inference('simplify_reflect+', [status(thm)], ['39', '40'])).
% 6.82/7.00  thf('42', plain, ((r2_hidden @ sk_F @ sk_B)),
% 6.82/7.00      inference('clc', [status(thm)], ['33', '41'])).
% 6.82/7.00  thf('43', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 6.82/7.00      inference('demod', [status(thm)], ['18', '19'])).
% 6.82/7.00  thf(d19_relat_1, axiom,
% 6.82/7.00    (![A:$i,B:$i]:
% 6.82/7.00     ( ( v1_relat_1 @ B ) =>
% 6.82/7.00       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 6.82/7.00  thf('44', plain,
% 6.82/7.00      (![X3 : $i, X4 : $i]:
% 6.82/7.00         (~ (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 6.82/7.00          | (v5_relat_1 @ X3 @ X4)
% 6.82/7.00          | ~ (v1_relat_1 @ X3))),
% 6.82/7.00      inference('cnf', [status(esa)], [d19_relat_1])).
% 6.82/7.00  thf('45', plain,
% 6.82/7.00      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 6.82/7.00      inference('sup-', [status(thm)], ['43', '44'])).
% 6.82/7.00  thf('46', plain,
% 6.82/7.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf(cc1_relset_1, axiom,
% 6.82/7.00    (![A:$i,B:$i,C:$i]:
% 6.82/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.82/7.00       ( v1_relat_1 @ C ) ))).
% 6.82/7.00  thf('47', plain,
% 6.82/7.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.82/7.00         ((v1_relat_1 @ X8)
% 6.82/7.00          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 6.82/7.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.82/7.00  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 6.82/7.00      inference('sup-', [status(thm)], ['46', '47'])).
% 6.82/7.00  thf('49', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 6.82/7.00      inference('demod', [status(thm)], ['45', '48'])).
% 6.82/7.00  thf('50', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf(d1_funct_2, axiom,
% 6.82/7.00    (![A:$i,B:$i,C:$i]:
% 6.82/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.82/7.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.82/7.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.82/7.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.82/7.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.82/7.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.82/7.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.82/7.00  thf(zf_stmt_1, axiom,
% 6.82/7.00    (![C:$i,B:$i,A:$i]:
% 6.82/7.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.82/7.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.82/7.00  thf('51', plain,
% 6.82/7.00      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.82/7.00         (~ (v1_funct_2 @ X24 @ X22 @ X23)
% 6.82/7.00          | ((X22) = (k1_relset_1 @ X22 @ X23 @ X24))
% 6.82/7.00          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.82/7.00  thf('52', plain,
% 6.82/7.00      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B)
% 6.82/7.00        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D)))),
% 6.82/7.00      inference('sup-', [status(thm)], ['50', '51'])).
% 6.82/7.00  thf('53', plain,
% 6.82/7.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('54', plain,
% 6.82/7.00      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.82/7.00         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 6.82/7.00          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.82/7.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.82/7.00  thf('55', plain,
% 6.82/7.00      (((k1_relset_1 @ sk_B @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 6.82/7.00      inference('sup-', [status(thm)], ['53', '54'])).
% 6.82/7.00  thf('56', plain,
% 6.82/7.00      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 6.82/7.00      inference('demod', [status(thm)], ['52', '55'])).
% 6.82/7.00  thf('57', plain,
% 6.82/7.00      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.82/7.00  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 6.82/7.00  thf(zf_stmt_4, axiom,
% 6.82/7.00    (![B:$i,A:$i]:
% 6.82/7.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.82/7.00       ( zip_tseitin_0 @ B @ A ) ))).
% 6.82/7.00  thf(zf_stmt_5, axiom,
% 6.82/7.00    (![A:$i,B:$i,C:$i]:
% 6.82/7.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.82/7.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.82/7.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.82/7.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.82/7.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.82/7.00  thf('58', plain,
% 6.82/7.00      (![X25 : $i, X26 : $i, X27 : $i]:
% 6.82/7.00         (~ (zip_tseitin_0 @ X25 @ X26)
% 6.82/7.00          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 6.82/7.00          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.82/7.00  thf('59', plain,
% 6.82/7.00      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 6.82/7.00      inference('sup-', [status(thm)], ['57', '58'])).
% 6.82/7.00  thf('60', plain,
% 6.82/7.00      (![X20 : $i, X21 : $i]:
% 6.82/7.00         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_4])).
% 6.82/7.00  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.82/7.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.82/7.00  thf('62', plain,
% 6.82/7.00      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.82/7.00      inference('sup+', [status(thm)], ['60', '61'])).
% 6.82/7.00  thf('63', plain, (~ (v1_xboole_0 @ sk_C)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('64', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 6.82/7.00      inference('sup-', [status(thm)], ['62', '63'])).
% 6.82/7.00  thf('65', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B)),
% 6.82/7.00      inference('demod', [status(thm)], ['59', '64'])).
% 6.82/7.00  thf('66', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 6.82/7.00      inference('demod', [status(thm)], ['56', '65'])).
% 6.82/7.00  thf(t172_funct_1, axiom,
% 6.82/7.00    (![A:$i,B:$i]:
% 6.82/7.00     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 6.82/7.00       ( ![C:$i]:
% 6.82/7.00         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 6.82/7.00           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 6.82/7.00  thf('67', plain,
% 6.82/7.00      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.82/7.00         (~ (r2_hidden @ X5 @ (k1_relat_1 @ X6))
% 6.82/7.00          | (r2_hidden @ (k1_funct_1 @ X6 @ X5) @ X7)
% 6.82/7.00          | ~ (v1_funct_1 @ X6)
% 6.82/7.00          | ~ (v5_relat_1 @ X6 @ X7)
% 6.82/7.00          | ~ (v1_relat_1 @ X6))),
% 6.82/7.00      inference('cnf', [status(esa)], [t172_funct_1])).
% 6.82/7.00  thf('68', plain,
% 6.82/7.00      (![X0 : $i, X1 : $i]:
% 6.82/7.00         (~ (r2_hidden @ X0 @ sk_B)
% 6.82/7.00          | ~ (v1_relat_1 @ sk_D)
% 6.82/7.00          | ~ (v5_relat_1 @ sk_D @ X1)
% 6.82/7.00          | ~ (v1_funct_1 @ sk_D)
% 6.82/7.00          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 6.82/7.00      inference('sup-', [status(thm)], ['66', '67'])).
% 6.82/7.00  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 6.82/7.00      inference('sup-', [status(thm)], ['46', '47'])).
% 6.82/7.00  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('71', plain,
% 6.82/7.00      (![X0 : $i, X1 : $i]:
% 6.82/7.00         (~ (r2_hidden @ X0 @ sk_B)
% 6.82/7.00          | ~ (v5_relat_1 @ sk_D @ X1)
% 6.82/7.00          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 6.82/7.00      inference('demod', [status(thm)], ['68', '69', '70'])).
% 6.82/7.00  thf('72', plain,
% 6.82/7.00      (![X0 : $i]:
% 6.82/7.00         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 6.82/7.00          | ~ (r2_hidden @ X0 @ sk_B))),
% 6.82/7.00      inference('sup-', [status(thm)], ['49', '71'])).
% 6.82/7.00  thf('73', plain,
% 6.82/7.00      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 6.82/7.00      inference('sup-', [status(thm)], ['42', '72'])).
% 6.82/7.00  thf(d8_partfun1, axiom,
% 6.82/7.00    (![A:$i,B:$i]:
% 6.82/7.00     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 6.82/7.00       ( ![C:$i]:
% 6.82/7.00         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 6.82/7.00           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 6.82/7.00  thf('74', plain,
% 6.82/7.00      (![X28 : $i, X29 : $i, X30 : $i]:
% 6.82/7.00         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 6.82/7.00          | ((k7_partfun1 @ X30 @ X29 @ X28) = (k1_funct_1 @ X29 @ X28))
% 6.82/7.00          | ~ (v1_funct_1 @ X29)
% 6.82/7.00          | ~ (v5_relat_1 @ X29 @ X30)
% 6.82/7.00          | ~ (v1_relat_1 @ X29))),
% 6.82/7.00      inference('cnf', [status(esa)], [d8_partfun1])).
% 6.82/7.00  thf('75', plain,
% 6.82/7.00      (![X0 : $i]:
% 6.82/7.00         (~ (v1_relat_1 @ sk_E)
% 6.82/7.00          | ~ (v5_relat_1 @ sk_E @ X0)
% 6.82/7.00          | ~ (v1_funct_1 @ sk_E)
% 6.82/7.00          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 6.82/7.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 6.82/7.00      inference('sup-', [status(thm)], ['73', '74'])).
% 6.82/7.00  thf('76', plain,
% 6.82/7.00      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('77', plain,
% 6.82/7.00      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.82/7.00         ((v1_relat_1 @ X8)
% 6.82/7.00          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 6.82/7.00      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.82/7.00  thf('78', plain, ((v1_relat_1 @ sk_E)),
% 6.82/7.00      inference('sup-', [status(thm)], ['76', '77'])).
% 6.82/7.00  thf('79', plain, ((v1_funct_1 @ sk_E)),
% 6.82/7.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.82/7.00  thf('80', plain,
% 6.82/7.00      (![X0 : $i]:
% 6.82/7.00         (~ (v5_relat_1 @ sk_E @ X0)
% 6.82/7.00          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 6.82/7.00              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 6.82/7.00      inference('demod', [status(thm)], ['75', '78', '79'])).
% 6.82/7.00  thf('81', plain,
% 6.82/7.00      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 6.82/7.00         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 6.82/7.00      inference('sup-', [status(thm)], ['30', '80'])).
% 6.82/7.00  thf('82', plain,
% 6.82/7.00      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 6.82/7.00         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 6.82/7.00      inference('demod', [status(thm)], ['27', '81'])).
% 6.82/7.00  thf('83', plain, ($false),
% 6.82/7.00      inference('simplify_reflect-', [status(thm)], ['26', '82'])).
% 6.82/7.00  
% 6.82/7.00  % SZS output end Refutation
% 6.82/7.00  
% 6.82/7.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

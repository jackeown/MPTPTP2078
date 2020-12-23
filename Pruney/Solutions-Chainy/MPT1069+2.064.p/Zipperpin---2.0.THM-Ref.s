%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3DtNjjGP7k

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:10 EST 2020

% Result     : Theorem 3.48s
% Output     : Refutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 208 expanded)
%              Number of leaves         :   46 (  82 expanded)
%              Depth                    :   14
%              Number of atoms          : 1157 (4125 expanded)
%              Number of equality atoms :   60 ( 178 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ X34 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X34 @ X35 @ X38 @ X33 @ X37 ) @ X36 )
        = ( k1_funct_1 @ X37 @ ( k1_funct_1 @ X33 @ X36 ) ) )
      | ( X34 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X34 @ X35 @ X33 ) @ ( k1_relset_1 @ X35 @ X38 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['6','9','10','11'])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['15','20','21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    v1_funct_2 @ sk_D @ sk_B @ sk_C_1 ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('51',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['49','58'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X11 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('65',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['61','66','67'])).

thf('69',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','68'])).

thf('70',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['69','76'])).

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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( ( k7_partfun1 @ X32 @ X31 @ X30 )
        = ( k1_funct_1 @ X31 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v5_relat_1 @ X31 @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
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
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3DtNjjGP7k
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:23:11 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.48/3.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.48/3.67  % Solved by: fo/fo7.sh
% 3.48/3.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.48/3.67  % done 3634 iterations in 3.215s
% 3.48/3.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.48/3.67  % SZS output start Refutation
% 3.48/3.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.48/3.67  thf(sk_F_type, type, sk_F: $i).
% 3.48/3.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.48/3.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.48/3.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.48/3.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.48/3.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.48/3.67  thf(sk_D_type, type, sk_D: $i).
% 3.48/3.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.48/3.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.48/3.67  thf(sk_E_type, type, sk_E: $i).
% 3.48/3.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.48/3.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.48/3.67  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 3.48/3.67  thf(sk_A_type, type, sk_A: $i).
% 3.48/3.67  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.48/3.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.48/3.67  thf(sk_B_type, type, sk_B: $i).
% 3.48/3.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.48/3.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.48/3.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.48/3.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.48/3.67  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 3.48/3.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.48/3.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.48/3.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.48/3.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.48/3.67  thf(t186_funct_2, conjecture,
% 3.48/3.67    (![A:$i,B:$i,C:$i]:
% 3.48/3.67     ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.48/3.67       ( ![D:$i]:
% 3.48/3.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.48/3.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.48/3.67           ( ![E:$i]:
% 3.48/3.67             ( ( ( v1_funct_1 @ E ) & 
% 3.48/3.67                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.48/3.67               ( ![F:$i]:
% 3.48/3.67                 ( ( m1_subset_1 @ F @ B ) =>
% 3.48/3.67                   ( ( r1_tarski @
% 3.48/3.67                       ( k2_relset_1 @ B @ C @ D ) @ 
% 3.48/3.67                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.48/3.67                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.48/3.67                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.48/3.67                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.48/3.67  thf(zf_stmt_0, negated_conjecture,
% 3.48/3.67    (~( ![A:$i,B:$i,C:$i]:
% 3.48/3.67        ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.48/3.67          ( ![D:$i]:
% 3.48/3.67            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.48/3.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.48/3.67              ( ![E:$i]:
% 3.48/3.67                ( ( ( v1_funct_1 @ E ) & 
% 3.48/3.67                    ( m1_subset_1 @
% 3.48/3.67                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.48/3.67                  ( ![F:$i]:
% 3.48/3.67                    ( ( m1_subset_1 @ F @ B ) =>
% 3.48/3.67                      ( ( r1_tarski @
% 3.48/3.67                          ( k2_relset_1 @ B @ C @ D ) @ 
% 3.48/3.67                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.48/3.67                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.48/3.67                          ( ( k1_funct_1 @
% 3.48/3.67                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.48/3.67                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 3.48/3.67    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 3.48/3.67  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('1', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(redefinition_k1_relset_1, axiom,
% 3.48/3.67    (![A:$i,B:$i,C:$i]:
% 3.48/3.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.48/3.67  thf('2', plain,
% 3.48/3.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.48/3.67         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.48/3.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.48/3.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.48/3.67  thf('3', plain,
% 3.48/3.67      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.48/3.67      inference('sup-', [status(thm)], ['1', '2'])).
% 3.48/3.67  thf('4', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(t185_funct_2, axiom,
% 3.48/3.67    (![A:$i,B:$i,C:$i]:
% 3.48/3.67     ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.48/3.67       ( ![D:$i]:
% 3.48/3.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.48/3.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.48/3.67           ( ![E:$i]:
% 3.48/3.67             ( ( ( v1_funct_1 @ E ) & 
% 3.48/3.67                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 3.48/3.67               ( ![F:$i]:
% 3.48/3.67                 ( ( m1_subset_1 @ F @ B ) =>
% 3.48/3.67                   ( ( r1_tarski @
% 3.48/3.67                       ( k2_relset_1 @ B @ C @ D ) @ 
% 3.48/3.67                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 3.48/3.67                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.48/3.67                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 3.48/3.67                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.48/3.67  thf('5', plain,
% 3.48/3.67      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.48/3.67         (~ (v1_funct_1 @ X33)
% 3.48/3.67          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 3.48/3.67          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 3.48/3.67          | ~ (m1_subset_1 @ X36 @ X34)
% 3.48/3.67          | ((k1_funct_1 @ (k8_funct_2 @ X34 @ X35 @ X38 @ X33 @ X37) @ X36)
% 3.48/3.67              = (k1_funct_1 @ X37 @ (k1_funct_1 @ X33 @ X36)))
% 3.48/3.67          | ((X34) = (k1_xboole_0))
% 3.48/3.67          | ~ (r1_tarski @ (k2_relset_1 @ X34 @ X35 @ X33) @ 
% 3.48/3.67               (k1_relset_1 @ X35 @ X38 @ X37))
% 3.48/3.67          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X38)))
% 3.48/3.67          | ~ (v1_funct_1 @ X37)
% 3.48/3.67          | (v1_xboole_0 @ X35))),
% 3.48/3.67      inference('cnf', [status(esa)], [t185_funct_2])).
% 3.48/3.67  thf('6', plain,
% 3.48/3.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.67         ((v1_xboole_0 @ sk_C_1)
% 3.48/3.67          | ~ (v1_funct_1 @ X0)
% 3.48/3.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 3.48/3.67          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 3.48/3.67               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 3.48/3.67          | ((sk_B) = (k1_xboole_0))
% 3.48/3.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 3.48/3.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 3.48/3.67          | ~ (m1_subset_1 @ X2 @ sk_B)
% 3.48/3.67          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C_1)
% 3.48/3.67          | ~ (v1_funct_1 @ sk_D))),
% 3.48/3.67      inference('sup-', [status(thm)], ['4', '5'])).
% 3.48/3.67  thf('7', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(redefinition_k2_relset_1, axiom,
% 3.48/3.67    (![A:$i,B:$i,C:$i]:
% 3.48/3.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.67       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.48/3.67  thf('8', plain,
% 3.48/3.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.48/3.67         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 3.48/3.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.48/3.67      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.48/3.67  thf('9', plain,
% 3.48/3.67      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.48/3.67      inference('sup-', [status(thm)], ['7', '8'])).
% 3.48/3.67  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('12', plain,
% 3.48/3.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.67         ((v1_xboole_0 @ sk_C_1)
% 3.48/3.67          | ~ (v1_funct_1 @ X0)
% 3.48/3.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 3.48/3.67          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.48/3.67               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 3.48/3.67          | ((sk_B) = (k1_xboole_0))
% 3.48/3.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 3.48/3.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 3.48/3.67          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 3.48/3.67      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 3.48/3.67  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('14', plain,
% 3.48/3.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.67         ((v1_xboole_0 @ sk_C_1)
% 3.48/3.67          | ~ (v1_funct_1 @ X0)
% 3.48/3.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 3.48/3.67          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.48/3.67               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 3.48/3.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 3.48/3.67              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 3.48/3.67          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 3.48/3.67      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 3.48/3.67  thf('15', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 3.48/3.67          | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.48/3.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 3.48/3.67              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 3.48/3.67          | ~ (m1_subset_1 @ sk_E @ 
% 3.48/3.67               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 3.48/3.67          | ~ (v1_funct_1 @ sk_E)
% 3.48/3.67          | (v1_xboole_0 @ sk_C_1))),
% 3.48/3.67      inference('sup-', [status(thm)], ['3', '14'])).
% 3.48/3.67  thf('16', plain,
% 3.48/3.67      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 3.48/3.67        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('17', plain,
% 3.48/3.67      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.48/3.67      inference('sup-', [status(thm)], ['1', '2'])).
% 3.48/3.67  thf('18', plain,
% 3.48/3.67      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 3.48/3.67      inference('demod', [status(thm)], ['16', '17'])).
% 3.48/3.67  thf('19', plain,
% 3.48/3.67      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.48/3.67      inference('sup-', [status(thm)], ['7', '8'])).
% 3.48/3.67  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 3.48/3.67      inference('demod', [status(thm)], ['18', '19'])).
% 3.48/3.67  thf('21', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('23', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.48/3.67          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 3.48/3.67              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 3.48/3.67          | (v1_xboole_0 @ sk_C_1))),
% 3.48/3.67      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 3.48/3.67  thf('24', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('25', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 3.48/3.67            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 3.48/3.67          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 3.48/3.67      inference('clc', [status(thm)], ['23', '24'])).
% 3.48/3.67  thf('26', plain,
% 3.48/3.67      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 3.48/3.67         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 3.48/3.67      inference('sup-', [status(thm)], ['0', '25'])).
% 3.48/3.67  thf('27', plain,
% 3.48/3.67      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 3.48/3.67         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('28', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(cc2_relset_1, axiom,
% 3.48/3.67    (![A:$i,B:$i,C:$i]:
% 3.48/3.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.48/3.67  thf('29', plain,
% 3.48/3.67      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.48/3.67         ((v5_relat_1 @ X13 @ X15)
% 3.48/3.67          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.48/3.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.48/3.67  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 3.48/3.67      inference('sup-', [status(thm)], ['28', '29'])).
% 3.48/3.67  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(t2_subset, axiom,
% 3.48/3.67    (![A:$i,B:$i]:
% 3.48/3.67     ( ( m1_subset_1 @ A @ B ) =>
% 3.48/3.67       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 3.48/3.67  thf('32', plain,
% 3.48/3.67      (![X5 : $i, X6 : $i]:
% 3.48/3.67         ((r2_hidden @ X5 @ X6)
% 3.48/3.67          | (v1_xboole_0 @ X6)
% 3.48/3.67          | ~ (m1_subset_1 @ X5 @ X6))),
% 3.48/3.67      inference('cnf', [status(esa)], [t2_subset])).
% 3.48/3.67  thf('33', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 3.48/3.67      inference('sup-', [status(thm)], ['31', '32'])).
% 3.48/3.67  thf(l13_xboole_0, axiom,
% 3.48/3.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.48/3.67  thf('34', plain,
% 3.48/3.67      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 3.48/3.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.48/3.67  thf('35', plain,
% 3.48/3.67      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 3.48/3.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.48/3.67  thf('36', plain,
% 3.48/3.67      (![X0 : $i, X1 : $i]:
% 3.48/3.67         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.48/3.67      inference('sup+', [status(thm)], ['34', '35'])).
% 3.48/3.67  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('38', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (((X0) != (k1_xboole_0))
% 3.48/3.67          | ~ (v1_xboole_0 @ X0)
% 3.48/3.67          | ~ (v1_xboole_0 @ sk_B))),
% 3.48/3.67      inference('sup-', [status(thm)], ['36', '37'])).
% 3.48/3.67  thf('39', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.48/3.67      inference('simplify', [status(thm)], ['38'])).
% 3.48/3.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.48/3.67  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.48/3.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.48/3.67  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.48/3.67      inference('simplify_reflect+', [status(thm)], ['39', '40'])).
% 3.48/3.67  thf('42', plain, ((r2_hidden @ sk_F @ sk_B)),
% 3.48/3.67      inference('clc', [status(thm)], ['33', '41'])).
% 3.48/3.67  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C_1)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(d1_funct_2, axiom,
% 3.48/3.67    (![A:$i,B:$i,C:$i]:
% 3.48/3.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.48/3.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.48/3.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.48/3.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.48/3.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.48/3.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.48/3.67  thf(zf_stmt_1, axiom,
% 3.48/3.67    (![C:$i,B:$i,A:$i]:
% 3.48/3.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.48/3.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.48/3.67  thf('44', plain,
% 3.48/3.67      (![X24 : $i, X25 : $i, X26 : $i]:
% 3.48/3.67         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 3.48/3.67          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 3.48/3.67          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.48/3.67  thf('45', plain,
% 3.48/3.67      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B)
% 3.48/3.67        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 3.48/3.67      inference('sup-', [status(thm)], ['43', '44'])).
% 3.48/3.67  thf('46', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('47', plain,
% 3.48/3.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.48/3.67         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 3.48/3.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.48/3.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.48/3.67  thf('48', plain,
% 3.48/3.67      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.48/3.67      inference('sup-', [status(thm)], ['46', '47'])).
% 3.48/3.67  thf('49', plain,
% 3.48/3.67      ((~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B)
% 3.48/3.67        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 3.48/3.67      inference('demod', [status(thm)], ['45', '48'])).
% 3.48/3.67  thf('50', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.48/3.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 3.48/3.67  thf(zf_stmt_4, axiom,
% 3.48/3.67    (![B:$i,A:$i]:
% 3.48/3.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.48/3.67       ( zip_tseitin_0 @ B @ A ) ))).
% 3.48/3.67  thf(zf_stmt_5, axiom,
% 3.48/3.67    (![A:$i,B:$i,C:$i]:
% 3.48/3.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.48/3.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.48/3.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.48/3.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.48/3.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.48/3.67  thf('51', plain,
% 3.48/3.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 3.48/3.67         (~ (zip_tseitin_0 @ X27 @ X28)
% 3.48/3.67          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 3.48/3.67          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.48/3.67  thf('52', plain,
% 3.48/3.67      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B)
% 3.48/3.67        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 3.48/3.67      inference('sup-', [status(thm)], ['50', '51'])).
% 3.48/3.67  thf('53', plain,
% 3.48/3.67      (![X22 : $i, X23 : $i]:
% 3.48/3.67         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.48/3.67  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.48/3.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.48/3.67  thf('55', plain,
% 3.48/3.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.48/3.67      inference('sup+', [status(thm)], ['53', '54'])).
% 3.48/3.67  thf('56', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('57', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 3.48/3.67      inference('sup-', [status(thm)], ['55', '56'])).
% 3.48/3.67  thf('58', plain, ((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_B)),
% 3.48/3.67      inference('demod', [status(thm)], ['52', '57'])).
% 3.48/3.67  thf('59', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.48/3.67      inference('demod', [status(thm)], ['49', '58'])).
% 3.48/3.67  thf(t12_funct_1, axiom,
% 3.48/3.67    (![A:$i,B:$i]:
% 3.48/3.67     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.48/3.67       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 3.48/3.67         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 3.48/3.67  thf('60', plain,
% 3.48/3.67      (![X11 : $i, X12 : $i]:
% 3.48/3.67         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 3.48/3.67          | (r2_hidden @ (k1_funct_1 @ X12 @ X11) @ (k2_relat_1 @ X12))
% 3.48/3.67          | ~ (v1_funct_1 @ X12)
% 3.48/3.67          | ~ (v1_relat_1 @ X12))),
% 3.48/3.67      inference('cnf', [status(esa)], [t12_funct_1])).
% 3.48/3.67  thf('61', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (~ (r2_hidden @ X0 @ sk_B)
% 3.48/3.67          | ~ (v1_relat_1 @ sk_D)
% 3.48/3.67          | ~ (v1_funct_1 @ sk_D)
% 3.48/3.67          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 3.48/3.67      inference('sup-', [status(thm)], ['59', '60'])).
% 3.48/3.67  thf('62', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(cc2_relat_1, axiom,
% 3.48/3.67    (![A:$i]:
% 3.48/3.67     ( ( v1_relat_1 @ A ) =>
% 3.48/3.67       ( ![B:$i]:
% 3.48/3.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.48/3.67  thf('63', plain,
% 3.48/3.67      (![X7 : $i, X8 : $i]:
% 3.48/3.67         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 3.48/3.67          | (v1_relat_1 @ X7)
% 3.48/3.67          | ~ (v1_relat_1 @ X8))),
% 3.48/3.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.48/3.67  thf('64', plain,
% 3.48/3.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) | (v1_relat_1 @ sk_D))),
% 3.48/3.67      inference('sup-', [status(thm)], ['62', '63'])).
% 3.48/3.67  thf(fc6_relat_1, axiom,
% 3.48/3.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.48/3.67  thf('65', plain,
% 3.48/3.67      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 3.48/3.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.48/3.67  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 3.48/3.67      inference('demod', [status(thm)], ['64', '65'])).
% 3.48/3.67  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('68', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (~ (r2_hidden @ X0 @ sk_B)
% 3.48/3.67          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 3.48/3.67      inference('demod', [status(thm)], ['61', '66', '67'])).
% 3.48/3.67  thf('69', plain,
% 3.48/3.67      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))),
% 3.48/3.67      inference('sup-', [status(thm)], ['42', '68'])).
% 3.48/3.67  thf('70', plain,
% 3.48/3.67      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) @ 
% 3.48/3.67        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf(d3_tarski, axiom,
% 3.48/3.67    (![A:$i,B:$i]:
% 3.48/3.67     ( ( r1_tarski @ A @ B ) <=>
% 3.48/3.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.48/3.67  thf('71', plain,
% 3.48/3.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.48/3.67         (~ (r2_hidden @ X0 @ X1)
% 3.48/3.67          | (r2_hidden @ X0 @ X2)
% 3.48/3.67          | ~ (r1_tarski @ X1 @ X2))),
% 3.48/3.67      inference('cnf', [status(esa)], [d3_tarski])).
% 3.48/3.67  thf('72', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         ((r2_hidden @ X0 @ (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))
% 3.48/3.67          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 3.48/3.67      inference('sup-', [status(thm)], ['70', '71'])).
% 3.48/3.67  thf('73', plain,
% 3.48/3.67      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 3.48/3.67      inference('sup-', [status(thm)], ['1', '2'])).
% 3.48/3.67  thf('74', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 3.48/3.67          | ~ (r2_hidden @ X0 @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D)))),
% 3.48/3.67      inference('demod', [status(thm)], ['72', '73'])).
% 3.48/3.67  thf('75', plain,
% 3.48/3.67      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.48/3.67      inference('sup-', [status(thm)], ['7', '8'])).
% 3.48/3.67  thf('76', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 3.48/3.67          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 3.48/3.67      inference('demod', [status(thm)], ['74', '75'])).
% 3.48/3.67  thf('77', plain,
% 3.48/3.67      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 3.48/3.67      inference('sup-', [status(thm)], ['69', '76'])).
% 3.48/3.67  thf(d8_partfun1, axiom,
% 3.48/3.67    (![A:$i,B:$i]:
% 3.48/3.67     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 3.48/3.67       ( ![C:$i]:
% 3.48/3.67         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 3.48/3.67           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 3.48/3.67  thf('78', plain,
% 3.48/3.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.48/3.67         (~ (r2_hidden @ X30 @ (k1_relat_1 @ X31))
% 3.48/3.67          | ((k7_partfun1 @ X32 @ X31 @ X30) = (k1_funct_1 @ X31 @ X30))
% 3.48/3.67          | ~ (v1_funct_1 @ X31)
% 3.48/3.67          | ~ (v5_relat_1 @ X31 @ X32)
% 3.48/3.67          | ~ (v1_relat_1 @ X31))),
% 3.48/3.67      inference('cnf', [status(esa)], [d8_partfun1])).
% 3.48/3.67  thf('79', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (~ (v1_relat_1 @ sk_E)
% 3.48/3.67          | ~ (v5_relat_1 @ sk_E @ X0)
% 3.48/3.67          | ~ (v1_funct_1 @ sk_E)
% 3.48/3.67          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 3.48/3.67              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 3.48/3.67      inference('sup-', [status(thm)], ['77', '78'])).
% 3.48/3.67  thf('80', plain,
% 3.48/3.67      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('81', plain,
% 3.48/3.67      (![X7 : $i, X8 : $i]:
% 3.48/3.67         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 3.48/3.67          | (v1_relat_1 @ X7)
% 3.48/3.67          | ~ (v1_relat_1 @ X8))),
% 3.48/3.67      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.48/3.67  thf('82', plain,
% 3.48/3.67      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)) | (v1_relat_1 @ sk_E))),
% 3.48/3.67      inference('sup-', [status(thm)], ['80', '81'])).
% 3.48/3.67  thf('83', plain,
% 3.48/3.67      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 3.48/3.67      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.48/3.67  thf('84', plain, ((v1_relat_1 @ sk_E)),
% 3.48/3.67      inference('demod', [status(thm)], ['82', '83'])).
% 3.48/3.67  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 3.48/3.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.48/3.67  thf('86', plain,
% 3.48/3.67      (![X0 : $i]:
% 3.48/3.67         (~ (v5_relat_1 @ sk_E @ X0)
% 3.48/3.67          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 3.48/3.67              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 3.48/3.67      inference('demod', [status(thm)], ['79', '84', '85'])).
% 3.48/3.67  thf('87', plain,
% 3.48/3.67      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 3.48/3.67         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 3.48/3.67      inference('sup-', [status(thm)], ['30', '86'])).
% 3.48/3.67  thf('88', plain,
% 3.48/3.67      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ sk_F)
% 3.48/3.67         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 3.48/3.67      inference('demod', [status(thm)], ['27', '87'])).
% 3.48/3.67  thf('89', plain, ($false),
% 3.48/3.67      inference('simplify_reflect-', [status(thm)], ['26', '88'])).
% 3.48/3.67  
% 3.48/3.67  % SZS output end Refutation
% 3.48/3.67  
% 3.51/3.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

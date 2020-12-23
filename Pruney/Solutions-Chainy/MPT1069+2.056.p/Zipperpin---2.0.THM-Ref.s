%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5vtLu2sTcd

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:08 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 231 expanded)
%              Number of leaves         :   49 (  90 expanded)
%              Depth                    :   16
%              Number of atoms          : 1183 (4345 expanded)
%              Number of equality atoms :   58 ( 182 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
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

thf('44',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('48',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('54',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('56',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('57',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1 ),
    inference(demod,[status(thm)],['52','61'])).

thf('63',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['49','62'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X13 ) @ X15 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v5_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['33','69'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('71',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('72',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ),
    inference(clc,[status(thm)],['70','80'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('82',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X36 ) )
      | ( ( k7_partfun1 @ X37 @ X36 @ X35 )
        = ( k1_funct_1 @ X36 @ X35 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v5_relat_1 @ X36 @ X37 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('88',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['83','88','89'])).

thf('91',plain,
    ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','90'])).

thf('92',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','91'])).

thf('93',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5vtLu2sTcd
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.40/2.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.40/2.59  % Solved by: fo/fo7.sh
% 2.40/2.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.40/2.59  % done 1748 iterations in 2.122s
% 2.40/2.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.40/2.59  % SZS output start Refutation
% 2.40/2.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.40/2.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.40/2.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.40/2.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.40/2.59  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 2.40/2.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.40/2.59  thf(sk_C_type, type, sk_C: $i).
% 2.40/2.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.40/2.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.40/2.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.40/2.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.40/2.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.40/2.59  thf(sk_D_type, type, sk_D: $i).
% 2.40/2.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.40/2.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.40/2.59  thf(sk_A_type, type, sk_A: $i).
% 2.40/2.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.40/2.59  thf(sk_F_type, type, sk_F: $i).
% 2.40/2.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.40/2.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.40/2.59  thf(sk_E_type, type, sk_E: $i).
% 2.40/2.59  thf(sk_B_type, type, sk_B: $i > $i).
% 2.40/2.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.40/2.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.40/2.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.40/2.59  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 2.40/2.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.40/2.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.40/2.59  thf(t186_funct_2, conjecture,
% 2.40/2.59    (![A:$i,B:$i,C:$i]:
% 2.40/2.59     ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.40/2.59       ( ![D:$i]:
% 2.40/2.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.40/2.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.40/2.59           ( ![E:$i]:
% 2.40/2.59             ( ( ( v1_funct_1 @ E ) & 
% 2.40/2.59                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 2.40/2.59               ( ![F:$i]:
% 2.40/2.59                 ( ( m1_subset_1 @ F @ B ) =>
% 2.40/2.59                   ( ( r1_tarski @
% 2.40/2.59                       ( k2_relset_1 @ B @ C @ D ) @ 
% 2.40/2.59                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 2.40/2.59                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.40/2.59                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 2.40/2.59                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.40/2.59  thf(zf_stmt_0, negated_conjecture,
% 2.40/2.59    (~( ![A:$i,B:$i,C:$i]:
% 2.40/2.59        ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.40/2.59          ( ![D:$i]:
% 2.40/2.59            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.40/2.59                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.40/2.59              ( ![E:$i]:
% 2.40/2.59                ( ( ( v1_funct_1 @ E ) & 
% 2.40/2.59                    ( m1_subset_1 @
% 2.40/2.59                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 2.40/2.59                  ( ![F:$i]:
% 2.40/2.59                    ( ( m1_subset_1 @ F @ B ) =>
% 2.40/2.59                      ( ( r1_tarski @
% 2.40/2.59                          ( k2_relset_1 @ B @ C @ D ) @ 
% 2.40/2.59                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 2.40/2.59                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.40/2.59                          ( ( k1_funct_1 @
% 2.40/2.59                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 2.40/2.59                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.40/2.59    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 2.40/2.59  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('1', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(redefinition_k1_relset_1, axiom,
% 2.40/2.59    (![A:$i,B:$i,C:$i]:
% 2.40/2.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.40/2.59  thf('2', plain,
% 2.40/2.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.40/2.59         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.40/2.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.40/2.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.40/2.59  thf('3', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.40/2.59      inference('sup-', [status(thm)], ['1', '2'])).
% 2.40/2.59  thf('4', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(t185_funct_2, axiom,
% 2.40/2.59    (![A:$i,B:$i,C:$i]:
% 2.40/2.59     ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.40/2.59       ( ![D:$i]:
% 2.40/2.59         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.40/2.59             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.40/2.59           ( ![E:$i]:
% 2.40/2.59             ( ( ( v1_funct_1 @ E ) & 
% 2.40/2.59                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 2.40/2.59               ( ![F:$i]:
% 2.40/2.59                 ( ( m1_subset_1 @ F @ B ) =>
% 2.40/2.59                   ( ( r1_tarski @
% 2.40/2.59                       ( k2_relset_1 @ B @ C @ D ) @ 
% 2.40/2.59                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 2.40/2.59                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.40/2.59                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 2.40/2.59                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.40/2.59  thf('5', plain,
% 2.40/2.59      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.40/2.59         (~ (v1_funct_1 @ X38)
% 2.40/2.59          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 2.40/2.59          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 2.40/2.59          | ~ (m1_subset_1 @ X41 @ X39)
% 2.40/2.59          | ((k1_funct_1 @ (k8_funct_2 @ X39 @ X40 @ X43 @ X38 @ X42) @ X41)
% 2.40/2.59              = (k1_funct_1 @ X42 @ (k1_funct_1 @ X38 @ X41)))
% 2.40/2.59          | ((X39) = (k1_xboole_0))
% 2.40/2.59          | ~ (r1_tarski @ (k2_relset_1 @ X39 @ X40 @ X38) @ 
% 2.40/2.59               (k1_relset_1 @ X40 @ X43 @ X42))
% 2.40/2.59          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X43)))
% 2.40/2.59          | ~ (v1_funct_1 @ X42)
% 2.40/2.59          | (v1_xboole_0 @ X40))),
% 2.40/2.59      inference('cnf', [status(esa)], [t185_funct_2])).
% 2.40/2.59  thf('6', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.59         ((v1_xboole_0 @ sk_C)
% 2.40/2.59          | ~ (v1_funct_1 @ X0)
% 2.40/2.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 2.40/2.59          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ 
% 2.40/2.59               (k1_relset_1 @ sk_C @ X1 @ X0))
% 2.40/2.59          | ((sk_B_1) = (k1_xboole_0))
% 2.40/2.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 2.40/2.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 2.40/2.59          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 2.40/2.59          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)
% 2.40/2.59          | ~ (v1_funct_1 @ sk_D))),
% 2.40/2.59      inference('sup-', [status(thm)], ['4', '5'])).
% 2.40/2.59  thf('7', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(redefinition_k2_relset_1, axiom,
% 2.40/2.59    (![A:$i,B:$i,C:$i]:
% 2.40/2.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.40/2.59  thf('8', plain,
% 2.40/2.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.40/2.59         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 2.40/2.59          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 2.40/2.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.40/2.59  thf('9', plain,
% 2.40/2.59      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.40/2.59      inference('sup-', [status(thm)], ['7', '8'])).
% 2.40/2.59  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('12', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.59         ((v1_xboole_0 @ sk_C)
% 2.40/2.59          | ~ (v1_funct_1 @ X0)
% 2.40/2.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 2.40/2.59          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 2.40/2.59          | ((sk_B_1) = (k1_xboole_0))
% 2.40/2.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 2.40/2.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 2.40/2.59          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 2.40/2.59      inference('demod', [status(thm)], ['6', '9', '10', '11'])).
% 2.40/2.59  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('14', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.59         ((v1_xboole_0 @ sk_C)
% 2.40/2.59          | ~ (v1_funct_1 @ X0)
% 2.40/2.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 2.40/2.59          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 2.40/2.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 2.40/2.59              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 2.40/2.59          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 2.40/2.59      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 2.40/2.59  thf('15', plain,
% 2.40/2.59      (![X0 : $i]:
% 2.40/2.59         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 2.40/2.59          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 2.40/2.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ 
% 2.40/2.59              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 2.40/2.59          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 2.40/2.59          | ~ (v1_funct_1 @ sk_E)
% 2.40/2.59          | (v1_xboole_0 @ sk_C))),
% 2.40/2.59      inference('sup-', [status(thm)], ['3', '14'])).
% 2.40/2.59  thf('16', plain,
% 2.40/2.59      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ 
% 2.40/2.59        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('17', plain,
% 2.40/2.59      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 2.40/2.59      inference('sup-', [status(thm)], ['1', '2'])).
% 2.40/2.59  thf('18', plain,
% 2.40/2.59      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 2.40/2.59      inference('demod', [status(thm)], ['16', '17'])).
% 2.40/2.59  thf('19', plain,
% 2.40/2.59      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.40/2.59      inference('sup-', [status(thm)], ['7', '8'])).
% 2.40/2.59  thf('20', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 2.40/2.59      inference('demod', [status(thm)], ['18', '19'])).
% 2.40/2.59  thf('21', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('22', plain, ((v1_funct_1 @ sk_E)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('23', plain,
% 2.40/2.59      (![X0 : $i]:
% 2.40/2.59         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 2.40/2.59          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ 
% 2.40/2.59              X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 2.40/2.59          | (v1_xboole_0 @ sk_C))),
% 2.40/2.59      inference('demod', [status(thm)], ['15', '20', '21', '22'])).
% 2.40/2.59  thf('24', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('25', plain,
% 2.40/2.59      (![X0 : $i]:
% 2.40/2.59         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 2.40/2.59            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 2.40/2.59          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 2.40/2.59      inference('clc', [status(thm)], ['23', '24'])).
% 2.40/2.59  thf('26', plain,
% 2.40/2.59      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 2.40/2.59         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.40/2.59      inference('sup-', [status(thm)], ['0', '25'])).
% 2.40/2.59  thf('27', plain,
% 2.40/2.59      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 2.40/2.59         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('28', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(cc2_relset_1, axiom,
% 2.40/2.59    (![A:$i,B:$i,C:$i]:
% 2.40/2.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.40/2.59  thf('29', plain,
% 2.40/2.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.40/2.59         ((v5_relat_1 @ X18 @ X20)
% 2.40/2.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.40/2.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.40/2.59  thf('30', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 2.40/2.59      inference('sup-', [status(thm)], ['28', '29'])).
% 2.40/2.59  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(t2_subset, axiom,
% 2.40/2.59    (![A:$i,B:$i]:
% 2.40/2.59     ( ( m1_subset_1 @ A @ B ) =>
% 2.40/2.59       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.40/2.59  thf('32', plain,
% 2.40/2.59      (![X5 : $i, X6 : $i]:
% 2.40/2.59         ((r2_hidden @ X5 @ X6)
% 2.40/2.59          | (v1_xboole_0 @ X6)
% 2.40/2.59          | ~ (m1_subset_1 @ X5 @ X6))),
% 2.40/2.59      inference('cnf', [status(esa)], [t2_subset])).
% 2.40/2.59  thf('33', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 2.40/2.59      inference('sup-', [status(thm)], ['31', '32'])).
% 2.40/2.59  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 2.40/2.59      inference('demod', [status(thm)], ['18', '19'])).
% 2.40/2.59  thf(d19_relat_1, axiom,
% 2.40/2.59    (![A:$i,B:$i]:
% 2.40/2.59     ( ( v1_relat_1 @ B ) =>
% 2.40/2.59       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.40/2.59  thf('35', plain,
% 2.40/2.59      (![X9 : $i, X10 : $i]:
% 2.40/2.59         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 2.40/2.59          | (v5_relat_1 @ X9 @ X10)
% 2.40/2.59          | ~ (v1_relat_1 @ X9))),
% 2.40/2.59      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.40/2.59  thf('36', plain,
% 2.40/2.59      ((~ (v1_relat_1 @ sk_D) | (v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E)))),
% 2.40/2.59      inference('sup-', [status(thm)], ['34', '35'])).
% 2.40/2.59  thf('37', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(cc2_relat_1, axiom,
% 2.40/2.59    (![A:$i]:
% 2.40/2.59     ( ( v1_relat_1 @ A ) =>
% 2.40/2.59       ( ![B:$i]:
% 2.40/2.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.40/2.59  thf('38', plain,
% 2.40/2.59      (![X7 : $i, X8 : $i]:
% 2.40/2.59         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.40/2.59          | (v1_relat_1 @ X7)
% 2.40/2.59          | ~ (v1_relat_1 @ X8))),
% 2.40/2.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.40/2.59  thf('39', plain,
% 2.40/2.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)) | (v1_relat_1 @ sk_D))),
% 2.40/2.59      inference('sup-', [status(thm)], ['37', '38'])).
% 2.40/2.59  thf(fc6_relat_1, axiom,
% 2.40/2.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.40/2.59  thf('40', plain,
% 2.40/2.59      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 2.40/2.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.40/2.59  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 2.40/2.59      inference('demod', [status(thm)], ['39', '40'])).
% 2.40/2.59  thf('42', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 2.40/2.59      inference('demod', [status(thm)], ['36', '41'])).
% 2.40/2.59  thf('43', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(d1_funct_2, axiom,
% 2.40/2.59    (![A:$i,B:$i,C:$i]:
% 2.40/2.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.40/2.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.40/2.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.40/2.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.40/2.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.40/2.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.40/2.59  thf(zf_stmt_1, axiom,
% 2.40/2.59    (![C:$i,B:$i,A:$i]:
% 2.40/2.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.40/2.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.40/2.59  thf('44', plain,
% 2.40/2.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.40/2.59         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 2.40/2.59          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 2.40/2.59          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.40/2.59  thf('45', plain,
% 2.40/2.59      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)
% 2.40/2.59        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D)))),
% 2.40/2.59      inference('sup-', [status(thm)], ['43', '44'])).
% 2.40/2.59  thf('46', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('47', plain,
% 2.40/2.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.40/2.59         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 2.40/2.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 2.40/2.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.40/2.59  thf('48', plain,
% 2.40/2.59      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 2.40/2.59      inference('sup-', [status(thm)], ['46', '47'])).
% 2.40/2.59  thf('49', plain,
% 2.40/2.59      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)
% 2.40/2.59        | ((sk_B_1) = (k1_relat_1 @ sk_D)))),
% 2.40/2.59      inference('demod', [status(thm)], ['45', '48'])).
% 2.40/2.59  thf('50', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.40/2.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.40/2.59  thf(zf_stmt_4, axiom,
% 2.40/2.59    (![B:$i,A:$i]:
% 2.40/2.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.40/2.59       ( zip_tseitin_0 @ B @ A ) ))).
% 2.40/2.59  thf(zf_stmt_5, axiom,
% 2.40/2.59    (![A:$i,B:$i,C:$i]:
% 2.40/2.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.40/2.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.40/2.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.40/2.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.40/2.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.40/2.59  thf('51', plain,
% 2.40/2.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.40/2.59         (~ (zip_tseitin_0 @ X32 @ X33)
% 2.40/2.59          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 2.40/2.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.40/2.59  thf('52', plain,
% 2.40/2.59      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)
% 2.40/2.59        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 2.40/2.59      inference('sup-', [status(thm)], ['50', '51'])).
% 2.40/2.59  thf('53', plain,
% 2.40/2.59      (![X27 : $i, X28 : $i]:
% 2.40/2.59         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.40/2.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.40/2.59  thf('54', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 2.40/2.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.40/2.59  thf('55', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.59         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 2.40/2.59      inference('sup+', [status(thm)], ['53', '54'])).
% 2.40/2.59  thf(d1_xboole_0, axiom,
% 2.40/2.59    (![A:$i]:
% 2.40/2.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.40/2.59  thf('56', plain,
% 2.40/2.59      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.40/2.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.40/2.59  thf(t7_ordinal1, axiom,
% 2.40/2.59    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.40/2.59  thf('57', plain,
% 2.40/2.59      (![X16 : $i, X17 : $i]:
% 2.40/2.59         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 2.40/2.59      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.40/2.59  thf('58', plain,
% 2.40/2.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 2.40/2.59      inference('sup-', [status(thm)], ['56', '57'])).
% 2.40/2.59  thf('59', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 2.40/2.59      inference('sup-', [status(thm)], ['55', '58'])).
% 2.40/2.59  thf('60', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('61', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 2.40/2.59      inference('sup-', [status(thm)], ['59', '60'])).
% 2.40/2.59  thf('62', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_B_1)),
% 2.40/2.59      inference('demod', [status(thm)], ['52', '61'])).
% 2.40/2.59  thf('63', plain, (((sk_B_1) = (k1_relat_1 @ sk_D))),
% 2.40/2.59      inference('demod', [status(thm)], ['49', '62'])).
% 2.40/2.59  thf(t172_funct_1, axiom,
% 2.40/2.59    (![A:$i,B:$i]:
% 2.40/2.59     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 2.40/2.59       ( ![C:$i]:
% 2.40/2.59         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 2.40/2.59           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 2.40/2.59  thf('64', plain,
% 2.40/2.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.40/2.59         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 2.40/2.59          | (r2_hidden @ (k1_funct_1 @ X14 @ X13) @ X15)
% 2.40/2.59          | ~ (v1_funct_1 @ X14)
% 2.40/2.59          | ~ (v5_relat_1 @ X14 @ X15)
% 2.40/2.59          | ~ (v1_relat_1 @ X14))),
% 2.40/2.59      inference('cnf', [status(esa)], [t172_funct_1])).
% 2.40/2.59  thf('65', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i]:
% 2.40/2.59         (~ (r2_hidden @ X0 @ sk_B_1)
% 2.40/2.59          | ~ (v1_relat_1 @ sk_D)
% 2.40/2.59          | ~ (v5_relat_1 @ sk_D @ X1)
% 2.40/2.59          | ~ (v1_funct_1 @ sk_D)
% 2.40/2.59          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 2.40/2.59      inference('sup-', [status(thm)], ['63', '64'])).
% 2.40/2.59  thf('66', plain, ((v1_relat_1 @ sk_D)),
% 2.40/2.59      inference('demod', [status(thm)], ['39', '40'])).
% 2.40/2.59  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('68', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i]:
% 2.40/2.59         (~ (r2_hidden @ X0 @ sk_B_1)
% 2.40/2.59          | ~ (v5_relat_1 @ sk_D @ X1)
% 2.40/2.59          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 2.40/2.59      inference('demod', [status(thm)], ['65', '66', '67'])).
% 2.40/2.59  thf('69', plain,
% 2.40/2.59      (![X0 : $i]:
% 2.40/2.59         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_relat_1 @ sk_E))
% 2.40/2.59          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 2.40/2.59      inference('sup-', [status(thm)], ['42', '68'])).
% 2.40/2.59  thf('70', plain,
% 2.40/2.59      (((v1_xboole_0 @ sk_B_1)
% 2.40/2.59        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 2.40/2.59      inference('sup-', [status(thm)], ['33', '69'])).
% 2.40/2.59  thf(l13_xboole_0, axiom,
% 2.40/2.59    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.40/2.59  thf('71', plain,
% 2.40/2.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.40/2.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.40/2.59  thf('72', plain,
% 2.40/2.59      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 2.40/2.59      inference('cnf', [status(esa)], [l13_xboole_0])).
% 2.40/2.59  thf('73', plain,
% 2.40/2.59      (![X0 : $i, X1 : $i]:
% 2.40/2.59         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 2.40/2.59      inference('sup+', [status(thm)], ['71', '72'])).
% 2.40/2.59  thf('74', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('75', plain,
% 2.40/2.59      (![X0 : $i]:
% 2.40/2.59         (((X0) != (k1_xboole_0))
% 2.40/2.59          | ~ (v1_xboole_0 @ X0)
% 2.40/2.59          | ~ (v1_xboole_0 @ sk_B_1))),
% 2.40/2.59      inference('sup-', [status(thm)], ['73', '74'])).
% 2.40/2.59  thf('76', plain,
% 2.40/2.59      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.40/2.59      inference('simplify', [status(thm)], ['75'])).
% 2.40/2.59  thf('77', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 2.40/2.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.40/2.59  thf('78', plain,
% 2.40/2.59      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 2.40/2.59      inference('sup-', [status(thm)], ['56', '57'])).
% 2.40/2.59  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.40/2.59      inference('sup-', [status(thm)], ['77', '78'])).
% 2.40/2.59  thf('80', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 2.40/2.59      inference('demod', [status(thm)], ['76', '79'])).
% 2.40/2.59  thf('81', plain,
% 2.40/2.59      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))),
% 2.40/2.59      inference('clc', [status(thm)], ['70', '80'])).
% 2.40/2.59  thf(d8_partfun1, axiom,
% 2.40/2.59    (![A:$i,B:$i]:
% 2.40/2.59     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 2.40/2.59       ( ![C:$i]:
% 2.40/2.59         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 2.40/2.59           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 2.40/2.59  thf('82', plain,
% 2.40/2.59      (![X35 : $i, X36 : $i, X37 : $i]:
% 2.40/2.59         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X36))
% 2.40/2.59          | ((k7_partfun1 @ X37 @ X36 @ X35) = (k1_funct_1 @ X36 @ X35))
% 2.40/2.59          | ~ (v1_funct_1 @ X36)
% 2.40/2.59          | ~ (v5_relat_1 @ X36 @ X37)
% 2.40/2.59          | ~ (v1_relat_1 @ X36))),
% 2.40/2.59      inference('cnf', [status(esa)], [d8_partfun1])).
% 2.40/2.59  thf('83', plain,
% 2.40/2.59      (![X0 : $i]:
% 2.40/2.59         (~ (v1_relat_1 @ sk_E)
% 2.40/2.59          | ~ (v5_relat_1 @ sk_E @ X0)
% 2.40/2.59          | ~ (v1_funct_1 @ sk_E)
% 2.40/2.59          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 2.40/2.59              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 2.40/2.59      inference('sup-', [status(thm)], ['81', '82'])).
% 2.40/2.59  thf('84', plain,
% 2.40/2.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('85', plain,
% 2.40/2.59      (![X7 : $i, X8 : $i]:
% 2.40/2.59         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.40/2.59          | (v1_relat_1 @ X7)
% 2.40/2.59          | ~ (v1_relat_1 @ X8))),
% 2.40/2.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.40/2.59  thf('86', plain,
% 2.40/2.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 2.40/2.59      inference('sup-', [status(thm)], ['84', '85'])).
% 2.40/2.59  thf('87', plain,
% 2.40/2.59      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 2.40/2.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.40/2.59  thf('88', plain, ((v1_relat_1 @ sk_E)),
% 2.40/2.59      inference('demod', [status(thm)], ['86', '87'])).
% 2.40/2.59  thf('89', plain, ((v1_funct_1 @ sk_E)),
% 2.40/2.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.59  thf('90', plain,
% 2.40/2.59      (![X0 : $i]:
% 2.40/2.59         (~ (v5_relat_1 @ sk_E @ X0)
% 2.40/2.59          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 2.40/2.59              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 2.40/2.59      inference('demod', [status(thm)], ['83', '88', '89'])).
% 2.40/2.59  thf('91', plain,
% 2.40/2.59      (((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 2.40/2.59         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.40/2.59      inference('sup-', [status(thm)], ['30', '90'])).
% 2.40/2.59  thf('92', plain,
% 2.40/2.59      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 2.40/2.59         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 2.40/2.59      inference('demod', [status(thm)], ['27', '91'])).
% 2.40/2.59  thf('93', plain, ($false),
% 2.40/2.59      inference('simplify_reflect-', [status(thm)], ['26', '92'])).
% 2.40/2.59  
% 2.40/2.59  % SZS output end Refutation
% 2.40/2.59  
% 2.40/2.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

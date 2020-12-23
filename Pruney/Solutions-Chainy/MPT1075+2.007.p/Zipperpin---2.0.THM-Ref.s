%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z4pVbQVlNE

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:27 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 311 expanded)
%              Number of leaves         :   45 ( 109 expanded)
%              Depth                    :   14
%              Number of atoms          : 1734 (6887 expanded)
%              Number of equality atoms :   56 ( 164 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t192_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                 => ! [F: $i] :
                      ( ( m1_subset_1 @ F @ B )
                     => ( ( v1_partfun1 @ E @ A )
                       => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                          = ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i,D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                   => ! [F: $i] :
                        ( ( m1_subset_1 @ F @ B )
                       => ( ( v1_partfun1 @ E @ A )
                         => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                            = ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t192_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t189_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ( v1_xboole_0 @ X49 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_2 @ X50 @ X51 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X49 ) ) )
      | ( r2_hidden @ ( k3_funct_2 @ X51 @ X49 @ X50 @ X52 ) @ ( k2_relset_1 @ X51 @ X49 @ X50 ) )
      | ~ ( m1_subset_1 @ X52 @ X51 )
      | ( v1_xboole_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t189_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','6','7','8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('13',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( ( k3_funct_2 @ X40 @ X41 @ X39 @ X42 )
        = ( k1_funct_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['10','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ( v5_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v5_relat_1 @ X14 @ X16 )
      | ~ ( v5_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v5_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ X0 )
      | ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) @ X0 )
      | ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v5_relat_1 @ sk_D @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    v5_relat_1 @ sk_D @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','47'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ X22 )
      | ~ ( r1_tarski @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('56',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_partfun1 @ X33 @ X32 )
      | ( ( k1_relat_1 @ X33 )
        = X32 )
      | ~ ( v4_relat_1 @ X33 @ X32 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_A )
    | ( ( k1_relat_1 @ sk_E )
      = sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('62',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['57','62','65'])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['54','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
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

thf('69',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X44 @ X45 @ X48 @ X43 @ X47 ) @ X46 )
        = ( k1_funct_1 @ X47 @ ( k1_funct_1 @ X43 @ X46 ) ) )
      | ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X44 @ X45 @ X43 ) @ ( k1_relset_1 @ X45 @ X48 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('72',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('78',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v5_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['42','43'])).

thf('82',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','82','83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['51','85'])).

thf('87',plain,(
    ( k3_funct_2 @ sk_B_1 @ sk_C_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('89',plain,(
    ( k3_funct_2 @ sk_B_1 @ sk_C_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C )
        & ( m1_subset_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf('93',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X38 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X35 @ X36 @ X38 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ X40 )
      | ( ( k3_funct_2 @ X40 @ X41 @ X39 @ X42 )
        = ( k1_funct_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X38 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X35 @ X36 @ X38 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X38 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X35 @ X36 @ X38 @ X34 @ X37 ) @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B_1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_B_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['102','112','122'])).

thf('124',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_C_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k3_funct_2 @ sk_B_1 @ sk_C_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['90','125'])).

thf('127',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['89','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['86','127'])).

thf('129',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['128','129'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('131',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('132',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['131'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('133',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('134',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['50','130','132','133','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z4pVbQVlNE
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.84  % Solved by: fo/fo7.sh
% 0.60/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.84  % done 628 iterations in 0.392s
% 0.60/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.84  % SZS output start Refutation
% 0.60/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.84  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.60/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.84  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.60/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.84  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.60/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.84  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.84  thf(sk_F_type, type, sk_F: $i).
% 0.60/0.84  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.60/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.84  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.84  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.60/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.84  thf(t192_funct_2, conjecture,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.60/0.84           ( ![C:$i,D:$i]:
% 0.60/0.84             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.60/0.84                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.60/0.84               ( ![E:$i]:
% 0.60/0.84                 ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.84                     ( m1_subset_1 @
% 0.60/0.84                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.60/0.84                   ( ![F:$i]:
% 0.60/0.84                     ( ( m1_subset_1 @ F @ B ) =>
% 0.60/0.84                       ( ( v1_partfun1 @ E @ A ) =>
% 0.60/0.84                         ( ( k3_funct_2 @
% 0.60/0.84                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.60/0.84                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.84    (~( ![A:$i]:
% 0.60/0.84        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.84          ( ![B:$i]:
% 0.60/0.84            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.60/0.84              ( ![C:$i,D:$i]:
% 0.60/0.84                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.60/0.84                    ( m1_subset_1 @
% 0.60/0.84                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.60/0.84                  ( ![E:$i]:
% 0.60/0.84                    ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.84                        ( m1_subset_1 @
% 0.60/0.84                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.60/0.84                      ( ![F:$i]:
% 0.60/0.84                        ( ( m1_subset_1 @ F @ B ) =>
% 0.60/0.84                          ( ( v1_partfun1 @ E @ A ) =>
% 0.60/0.84                            ( ( k3_funct_2 @
% 0.60/0.84                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.60/0.84                              ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.84    inference('cnf.neg', [status(esa)], [t192_funct_2])).
% 0.60/0.84  thf('0', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('1', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t189_funct_2, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.60/0.84           ( ![C:$i]:
% 0.60/0.84             ( ( m1_subset_1 @ C @ A ) =>
% 0.60/0.84               ( ![D:$i]:
% 0.60/0.84                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.84                     ( m1_subset_1 @
% 0.60/0.84                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.84                   ( r2_hidden @
% 0.60/0.84                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.60/0.84                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.60/0.84  thf('2', plain,
% 0.60/0.84      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ X49)
% 0.60/0.84          | ~ (v1_funct_1 @ X50)
% 0.60/0.84          | ~ (v1_funct_2 @ X50 @ X51 @ X49)
% 0.60/0.84          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X49)))
% 0.60/0.84          | (r2_hidden @ (k3_funct_2 @ X51 @ X49 @ X50 @ X52) @ 
% 0.60/0.84             (k2_relset_1 @ X51 @ X49 @ X50))
% 0.60/0.84          | ~ (m1_subset_1 @ X52 @ X51)
% 0.60/0.84          | (v1_xboole_0 @ X51))),
% 0.60/0.84      inference('cnf', [status(esa)], [t189_funct_2])).
% 0.60/0.84  thf('3', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | (r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0) @ 
% 0.60/0.84             (k2_relset_1 @ sk_B_1 @ sk_A @ sk_D))
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D)
% 0.60/0.84          | (v1_xboole_0 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.84  thf('4', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k2_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.60/0.84  thf('5', plain,
% 0.60/0.84      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.60/0.84         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.60/0.84          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.60/0.84  thf('6', plain,
% 0.60/0.84      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.84  thf('7', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | (r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0) @ 
% 0.60/0.84             (k2_relat_1 @ sk_D))
% 0.60/0.84          | (v1_xboole_0 @ sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['3', '6', '7', '8'])).
% 0.60/0.84  thf('10', plain,
% 0.60/0.84      (((v1_xboole_0 @ sk_A)
% 0.60/0.84        | (r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F) @ 
% 0.60/0.84           (k2_relat_1 @ sk_D))
% 0.60/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['0', '9'])).
% 0.60/0.84  thf('11', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('12', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k3_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.60/0.84         ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.60/0.84         ( m1_subset_1 @ D @ A ) ) =>
% 0.60/0.84       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.60/0.84  thf('13', plain,
% 0.60/0.84      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.60/0.84          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.60/0.84          | ~ (v1_funct_1 @ X39)
% 0.60/0.84          | (v1_xboole_0 @ X40)
% 0.60/0.84          | ~ (m1_subset_1 @ X42 @ X40)
% 0.60/0.84          | ((k3_funct_2 @ X40 @ X41 @ X39 @ X42) = (k1_funct_1 @ X39 @ X42)))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | (v1_xboole_0 @ sk_B_1)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D)
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.84  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('16', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | (v1_xboole_0 @ sk_B_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.60/0.84  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | ((k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ X0)
% 0.60/0.84              = (k1_funct_1 @ sk_D @ X0)))),
% 0.60/0.84      inference('clc', [status(thm)], ['17', '18'])).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      (((k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.60/0.84      inference('sup-', [status(thm)], ['11', '19'])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      (((v1_xboole_0 @ sk_A)
% 0.60/0.84        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))
% 0.60/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['10', '20'])).
% 0.60/0.84  thf('22', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('23', plain,
% 0.60/0.84      (((v1_xboole_0 @ sk_B_1)
% 0.60/0.84        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D)))),
% 0.60/0.84      inference('clc', [status(thm)], ['21', '22'])).
% 0.60/0.84  thf('24', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('25', plain,
% 0.60/0.84      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))),
% 0.60/0.84      inference('clc', [status(thm)], ['23', '24'])).
% 0.60/0.84  thf(d10_xboole_0, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.60/0.84      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.84  thf('27', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.60/0.84      inference('simplify', [status(thm)], ['26'])).
% 0.60/0.84  thf(d19_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ B ) =>
% 0.60/0.84       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      (![X17 : $i, X18 : $i]:
% 0.60/0.84         (~ (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.60/0.84          | (v5_relat_1 @ X17 @ X18)
% 0.60/0.84          | ~ (v1_relat_1 @ X17))),
% 0.60/0.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc6_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.60/0.84       ( ![C:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.60/0.84          | (v5_relat_1 @ X14 @ X16)
% 0.60/0.84          | ~ (v5_relat_1 @ X15 @ X16)
% 0.60/0.84          | ~ (v1_relat_1 @ X15))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))
% 0.60/0.84          | ~ (v5_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ X0)
% 0.60/0.84          | (v5_relat_1 @ sk_D @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.84  thf(fc6_relat_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (v5_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A) @ X0)
% 0.60/0.84          | (v5_relat_1 @ sk_D @ X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['32', '33'])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))
% 0.60/0.84        | (v5_relat_1 @ sk_D @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['29', '34'])).
% 0.60/0.84  thf('36', plain,
% 0.60/0.84      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      ((v5_relat_1 @ sk_D @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X17 : $i, X18 : $i]:
% 0.60/0.84         (~ (v5_relat_1 @ X17 @ X18)
% 0.60/0.84          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.60/0.84          | ~ (v1_relat_1 @ X17))),
% 0.60/0.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_D)
% 0.60/0.84        | (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.60/0.84           (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc2_relat_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_relat_1 @ A ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      (![X12 : $i, X13 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.60/0.84          | (v1_relat_1 @ X12)
% 0.60/0.84          | ~ (v1_relat_1 @ X13))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.84  thf('42', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.84  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.84      inference('demod', [status(thm)], ['42', '43'])).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      ((r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.60/0.84        (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['39', '44'])).
% 0.60/0.84  thf(d3_tarski, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.84  thf('46', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X0 @ X1)
% 0.60/0.84          | (r2_hidden @ X0 @ X2)
% 0.60/0.84          | ~ (r1_tarski @ X1 @ X2))),
% 0.60/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.84  thf('47', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((r2_hidden @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.60/0.84          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['45', '46'])).
% 0.60/0.84  thf('48', plain,
% 0.60/0.84      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ 
% 0.60/0.84        (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['25', '47'])).
% 0.60/0.84  thf(t7_ordinal1, axiom,
% 0.60/0.84    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.84  thf('49', plain,
% 0.60/0.84      (![X21 : $i, X22 : $i]:
% 0.60/0.84         (~ (r2_hidden @ X21 @ X22) | ~ (r1_tarski @ X22 @ X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.84  thf('50', plain,
% 0.60/0.84      (~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) @ 
% 0.60/0.84          (k1_funct_1 @ sk_D @ sk_F))),
% 0.60/0.84      inference('sup-', [status(thm)], ['48', '49'])).
% 0.60/0.84  thf('51', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('52', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.84  thf('53', plain,
% 0.60/0.84      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.84         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.60/0.84          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.84  thf('54', plain,
% 0.60/0.84      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.60/0.84      inference('sup-', [status(thm)], ['52', '53'])).
% 0.60/0.84  thf('55', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(d4_partfun1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.60/0.84       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.60/0.84  thf('56', plain,
% 0.60/0.84      (![X32 : $i, X33 : $i]:
% 0.60/0.84         (~ (v1_partfun1 @ X33 @ X32)
% 0.60/0.84          | ((k1_relat_1 @ X33) = (X32))
% 0.60/0.84          | ~ (v4_relat_1 @ X33 @ X32)
% 0.60/0.84          | ~ (v1_relat_1 @ X33))),
% 0.60/0.84      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.60/0.84  thf('57', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_E)
% 0.60/0.84        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.60/0.84        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['55', '56'])).
% 0.60/0.84  thf('58', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('59', plain,
% 0.60/0.84      (![X12 : $i, X13 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.60/0.84          | (v1_relat_1 @ X12)
% 0.60/0.84          | ~ (v1_relat_1 @ X13))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.84  thf('60', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)) | (v1_relat_1 @ sk_E))),
% 0.60/0.84      inference('sup-', [status(thm)], ['58', '59'])).
% 0.60/0.84  thf('61', plain,
% 0.60/0.84      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.84  thf('62', plain, ((v1_relat_1 @ sk_E)),
% 0.60/0.84      inference('demod', [status(thm)], ['60', '61'])).
% 0.60/0.84  thf('63', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc2_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.84  thf('64', plain,
% 0.60/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.84         ((v4_relat_1 @ X23 @ X24)
% 0.60/0.84          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.84  thf('65', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.60/0.84      inference('sup-', [status(thm)], ['63', '64'])).
% 0.60/0.84  thf('66', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['57', '62', '65'])).
% 0.60/0.84  thf('67', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_E) = (sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['54', '66'])).
% 0.60/0.84  thf('68', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t185_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.60/0.84       ( ![D:$i]:
% 0.60/0.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.60/0.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.84           ( ![E:$i]:
% 0.60/0.84             ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.84                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.60/0.84               ( ![F:$i]:
% 0.60/0.84                 ( ( m1_subset_1 @ F @ B ) =>
% 0.60/0.84                   ( ( r1_tarski @
% 0.60/0.84                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.60/0.84                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.60/0.84                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.60/0.84                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.60/0.84                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.84  thf('69', plain,
% 0.60/0.84      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X43)
% 0.60/0.84          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.60/0.84          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.60/0.84          | ~ (m1_subset_1 @ X46 @ X44)
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ X44 @ X45 @ X48 @ X43 @ X47) @ X46)
% 0.60/0.84              = (k1_funct_1 @ X47 @ (k1_funct_1 @ X43 @ X46)))
% 0.60/0.84          | ((X44) = (k1_xboole_0))
% 0.60/0.84          | ~ (r1_tarski @ (k2_relset_1 @ X44 @ X45 @ X43) @ 
% 0.60/0.84               (k1_relset_1 @ X45 @ X48 @ X47))
% 0.60/0.84          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X48)))
% 0.60/0.84          | ~ (v1_funct_1 @ X47)
% 0.60/0.84          | (v1_xboole_0 @ X45))),
% 0.60/0.84      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.60/0.84  thf('70', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_A)
% 0.60/0.84          | ~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.60/0.84          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) @ 
% 0.60/0.84               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.60/0.84          | ((sk_B_1) = (k1_xboole_0))
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.60/0.84              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.60/0.84          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['68', '69'])).
% 0.60/0.84  thf('71', plain,
% 0.60/0.84      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.84  thf('72', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('73', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('74', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((v1_xboole_0 @ sk_A)
% 0.60/0.84          | ~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.60/0.84          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.60/0.84          | ((sk_B_1) = (k1_xboole_0))
% 0.60/0.84          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.60/0.84              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.60/0.84          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.60/0.84  thf('75', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | ((k1_funct_1 @ 
% 0.60/0.84              (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0)
% 0.60/0.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.60/0.84          | ((sk_B_1) = (k1_xboole_0))
% 0.60/0.84          | ~ (m1_subset_1 @ sk_E @ 
% 0.60/0.84               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))
% 0.60/0.84          | ~ (v1_funct_1 @ sk_E)
% 0.60/0.84          | (v1_xboole_0 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['67', '74'])).
% 0.60/0.84  thf('76', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('77', plain,
% 0.60/0.84      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.84         ((v5_relat_1 @ X23 @ X25)
% 0.60/0.84          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.84  thf('78', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.60/0.84      inference('sup-', [status(thm)], ['76', '77'])).
% 0.60/0.84  thf('79', plain,
% 0.60/0.84      (![X17 : $i, X18 : $i]:
% 0.60/0.84         (~ (v5_relat_1 @ X17 @ X18)
% 0.60/0.84          | (r1_tarski @ (k2_relat_1 @ X17) @ X18)
% 0.60/0.84          | ~ (v1_relat_1 @ X17))),
% 0.60/0.84      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.60/0.84  thf('80', plain,
% 0.60/0.84      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['78', '79'])).
% 0.60/0.84  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.84      inference('demod', [status(thm)], ['42', '43'])).
% 0.60/0.84  thf('82', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.60/0.84      inference('demod', [status(thm)], ['80', '81'])).
% 0.60/0.84  thf('83', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('84', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('85', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | ((k1_funct_1 @ 
% 0.60/0.84              (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0)
% 0.60/0.84              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.60/0.84          | ((sk_B_1) = (k1_xboole_0))
% 0.60/0.84          | (v1_xboole_0 @ sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['75', '82', '83', '84'])).
% 0.60/0.84  thf('86', plain,
% 0.60/0.84      (((v1_xboole_0 @ sk_A)
% 0.60/0.84        | ((sk_B_1) = (k1_xboole_0))
% 0.60/0.84        | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.60/0.84            sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['51', '85'])).
% 0.60/0.84  thf('87', plain,
% 0.60/0.84      (((k3_funct_2 @ sk_B_1 @ sk_C_1 @ 
% 0.60/0.84         (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ sk_F)
% 0.60/0.84         != (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('88', plain,
% 0.60/0.84      (((k3_funct_2 @ sk_B_1 @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.60/0.84      inference('sup-', [status(thm)], ['11', '19'])).
% 0.60/0.84  thf('89', plain,
% 0.60/0.84      (((k3_funct_2 @ sk_B_1 @ sk_C_1 @ 
% 0.60/0.84         (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ sk_F)
% 0.60/0.84         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.60/0.84      inference('demod', [status(thm)], ['87', '88'])).
% 0.60/0.84  thf('90', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('91', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('92', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(dt_k8_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.60/0.84         ( v1_funct_1 @ E ) & 
% 0.60/0.84         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.84       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.60/0.84         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.60/0.84         ( m1_subset_1 @
% 0.60/0.84           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.60/0.84           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.60/0.84  thf('93', plain,
% 0.60/0.84      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.60/0.84          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.60/0.84          | ~ (v1_funct_1 @ X34)
% 0.60/0.84          | ~ (v1_funct_1 @ X37)
% 0.60/0.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X38)))
% 0.60/0.84          | (m1_subset_1 @ (k8_funct_2 @ X35 @ X36 @ X38 @ X34 @ X37) @ 
% 0.60/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X38))))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.60/0.84  thf('94', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((m1_subset_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.60/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0)))
% 0.60/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.60/0.84          | ~ (v1_funct_1 @ X1)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D)
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['92', '93'])).
% 0.60/0.84  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('96', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('97', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((m1_subset_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.60/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0)))
% 0.60/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.60/0.84          | ~ (v1_funct_1 @ X1))),
% 0.60/0.84      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.60/0.84  thf('98', plain,
% 0.60/0.84      ((~ (v1_funct_1 @ sk_E)
% 0.60/0.84        | (m1_subset_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.60/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['91', '97'])).
% 0.60/0.84  thf('99', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('100', plain,
% 0.60/0.84      ((m1_subset_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.60/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.60/0.84      inference('demod', [status(thm)], ['98', '99'])).
% 0.60/0.84  thf('101', plain,
% 0.60/0.84      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.60/0.84          | ~ (v1_funct_2 @ X39 @ X40 @ X41)
% 0.60/0.84          | ~ (v1_funct_1 @ X39)
% 0.60/0.84          | (v1_xboole_0 @ X40)
% 0.60/0.84          | ~ (m1_subset_1 @ X42 @ X40)
% 0.60/0.84          | ((k3_funct_2 @ X40 @ X41 @ X39 @ X42) = (k1_funct_1 @ X39 @ X42)))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.60/0.84  thf('102', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((k3_funct_2 @ sk_B_1 @ sk_C_1 @ 
% 0.60/0.84            (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0)
% 0.60/0.84            = (k1_funct_1 @ 
% 0.60/0.84               (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | (v1_xboole_0 @ sk_B_1)
% 0.60/0.84          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E))
% 0.60/0.84          | ~ (v1_funct_2 @ 
% 0.60/0.84               (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ sk_B_1 @ 
% 0.60/0.84               sk_C_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['100', '101'])).
% 0.60/0.84  thf('103', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('104', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('105', plain,
% 0.60/0.84      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.60/0.84          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.60/0.84          | ~ (v1_funct_1 @ X34)
% 0.60/0.84          | ~ (v1_funct_1 @ X37)
% 0.60/0.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X38)))
% 0.60/0.84          | (v1_funct_1 @ (k8_funct_2 @ X35 @ X36 @ X38 @ X34 @ X37)))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.60/0.84  thf('106', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((v1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.60/0.84          | ~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D)
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['104', '105'])).
% 0.60/0.84  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('108', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('109', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((v1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X1 @ sk_D @ X0))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.60/0.84          | ~ (v1_funct_1 @ X0))),
% 0.60/0.84      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.60/0.84  thf('110', plain,
% 0.60/0.84      ((~ (v1_funct_1 @ sk_E)
% 0.60/0.84        | (v1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['103', '109'])).
% 0.60/0.84  thf('111', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('112', plain,
% 0.60/0.84      ((v1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E))),
% 0.60/0.84      inference('demod', [status(thm)], ['110', '111'])).
% 0.60/0.84  thf('113', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('114', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('115', plain,
% 0.60/0.84      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.60/0.84          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.60/0.84          | ~ (v1_funct_1 @ X34)
% 0.60/0.84          | ~ (v1_funct_1 @ X37)
% 0.60/0.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X38)))
% 0.60/0.84          | (v1_funct_2 @ (k8_funct_2 @ X35 @ X36 @ X38 @ X34 @ X37) @ X35 @ 
% 0.60/0.84             X38))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.60/0.84  thf('116', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((v1_funct_2 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.60/0.84           sk_B_1 @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.60/0.84          | ~ (v1_funct_1 @ X1)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D)
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['114', '115'])).
% 0.60/0.84  thf('117', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('118', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('119', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         ((v1_funct_2 @ (k8_funct_2 @ sk_B_1 @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.60/0.84           sk_B_1 @ X0)
% 0.60/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.60/0.84          | ~ (v1_funct_1 @ X1))),
% 0.60/0.84      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.60/0.84  thf('120', plain,
% 0.60/0.84      ((~ (v1_funct_1 @ sk_E)
% 0.60/0.84        | (v1_funct_2 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.60/0.84           sk_B_1 @ sk_C_1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['113', '119'])).
% 0.60/0.84  thf('121', plain, ((v1_funct_1 @ sk_E)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('122', plain,
% 0.60/0.84      ((v1_funct_2 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.60/0.84        sk_B_1 @ sk_C_1)),
% 0.60/0.84      inference('demod', [status(thm)], ['120', '121'])).
% 0.60/0.84  thf('123', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (((k3_funct_2 @ sk_B_1 @ sk_C_1 @ 
% 0.60/0.84            (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0)
% 0.60/0.84            = (k1_funct_1 @ 
% 0.60/0.84               (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | (v1_xboole_0 @ sk_B_1))),
% 0.60/0.84      inference('demod', [status(thm)], ['102', '112', '122'])).
% 0.60/0.84  thf('124', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('125', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.60/0.84          | ((k3_funct_2 @ sk_B_1 @ sk_C_1 @ 
% 0.60/0.84              (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0)
% 0.60/0.84              = (k1_funct_1 @ 
% 0.60/0.84                 (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ X0)))),
% 0.60/0.84      inference('clc', [status(thm)], ['123', '124'])).
% 0.60/0.84  thf('126', plain,
% 0.60/0.84      (((k3_funct_2 @ sk_B_1 @ sk_C_1 @ 
% 0.60/0.84         (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ sk_F)
% 0.60/0.84         = (k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.60/0.84            sk_F))),
% 0.60/0.84      inference('sup-', [status(thm)], ['90', '125'])).
% 0.60/0.84  thf('127', plain,
% 0.60/0.84      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D @ sk_E) @ 
% 0.60/0.84         sk_F) != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.60/0.84      inference('demod', [status(thm)], ['89', '126'])).
% 0.60/0.84  thf('128', plain, (((v1_xboole_0 @ sk_A) | ((sk_B_1) = (k1_xboole_0)))),
% 0.60/0.84      inference('simplify_reflect-', [status(thm)], ['86', '127'])).
% 0.60/0.84  thf('129', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('130', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.60/0.84      inference('clc', [status(thm)], ['128', '129'])).
% 0.60/0.84  thf(t113_zfmisc_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.84       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.84  thf('131', plain,
% 0.60/0.84      (![X9 : $i, X10 : $i]:
% 0.60/0.84         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.84  thf('132', plain,
% 0.60/0.84      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.60/0.84      inference('simplify', [status(thm)], ['131'])).
% 0.60/0.84  thf(t60_relat_1, axiom,
% 0.60/0.84    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.60/0.84     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.60/0.84  thf('133', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.84      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.60/0.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.84  thf('134', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.60/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.84  thf('135', plain, ($false),
% 0.60/0.84      inference('demod', [status(thm)], ['50', '130', '132', '133', '134'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8eQ4nKFsTY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 235 expanded)
%              Number of leaves         :   37 (  85 expanded)
%              Depth                    :   19
%              Number of atoms          : 1127 (5096 expanded)
%              Number of equality atoms :   32 ( 114 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t193_funct_2,conjecture,(
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
                          = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) )).

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
                            = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t193_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t192_funct_2,axiom,(
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

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_partfun1 @ X31 @ X32 )
      | ( ( k3_funct_2 @ X30 @ X33 @ ( k8_funct_2 @ X30 @ X32 @ X33 @ X34 @ X31 ) @ X35 )
        = ( k1_funct_1 @ X31 @ ( k3_funct_2 @ X30 @ X32 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ X30 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X30 @ X32 )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t192_funct_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X2 @ X1 )
      | ( ( k3_funct_2 @ X1 @ sk_C @ ( k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E ) @ X2 )
        = ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ X1 @ sk_A @ X0 @ X2 ) ) )
      | ~ ( v1_partfun1 @ sk_E @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X2 @ X1 )
      | ( ( k3_funct_2 @ X1 @ sk_C @ ( k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E ) @ X2 )
        = ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ X1 @ sk_A @ X0 @ X2 ) ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('16',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ X27 )
      | ( ( k3_funct_2 @ X27 @ X28 @ X26 @ X29 )
        = ( k1_funct_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('27',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('29',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['40','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ sk_B )
    | ( ( k1_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['44','47','50'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('64',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['62','63'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('65',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_A )
    | ( ( k1_relat_1 @ sk_E )
      = sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('79',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['76','79','82'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('84',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k7_partfun1 @ X25 @ X24 @ X23 )
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X1 @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['77','78'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_E @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ~ ( v5_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','88'])).

thf('90',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['29','89'])).

thf('91',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['25','26','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['24','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['0','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8eQ4nKFsTY
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 76 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(t193_funct_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i,D:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.20/0.49                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.20/0.49               ( ![E:$i]:
% 0.20/0.49                 ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                     ( m1_subset_1 @
% 0.20/0.49                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.20/0.49                   ( ![F:$i]:
% 0.20/0.49                     ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.49                       ( ( v1_partfun1 @ E @ A ) =>
% 0.20/0.49                         ( ( k3_funct_2 @
% 0.20/0.49                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.20/0.49                           ( k7_partfun1 @
% 0.20/0.49                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49              ( ![C:$i,D:$i]:
% 0.20/0.49                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.20/0.49                    ( m1_subset_1 @
% 0.20/0.49                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.20/0.49                  ( ![E:$i]:
% 0.20/0.49                    ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                        ( m1_subset_1 @
% 0.20/0.49                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.20/0.49                      ( ![F:$i]:
% 0.20/0.49                        ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.49                          ( ( v1_partfun1 @ E @ A ) =>
% 0.20/0.49                            ( ( k3_funct_2 @
% 0.20/0.49                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.20/0.49                              ( k7_partfun1 @
% 0.20/0.49                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.20/0.49  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t192_funct_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i,D:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.20/0.49                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.20/0.49               ( ![E:$i]:
% 0.20/0.49                 ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.49                     ( m1_subset_1 @
% 0.20/0.49                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.20/0.49                   ( ![F:$i]:
% 0.20/0.49                     ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.49                       ( ( v1_partfun1 @ E @ A ) =>
% 0.20/0.49                         ( ( k3_funct_2 @
% 0.20/0.49                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.20/0.49                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X30)
% 0.20/0.49          | ~ (v1_funct_1 @ X31)
% 0.20/0.49          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.20/0.49          | ~ (v1_partfun1 @ X31 @ X32)
% 0.20/0.49          | ((k3_funct_2 @ X30 @ X33 @ 
% 0.20/0.49              (k8_funct_2 @ X30 @ X32 @ X33 @ X34 @ X31) @ X35)
% 0.20/0.49              = (k1_funct_1 @ X31 @ (k3_funct_2 @ X30 @ X32 @ X34 @ X35)))
% 0.20/0.49          | ~ (m1_subset_1 @ X35 @ X30)
% 0.20/0.49          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X32)))
% 0.20/0.49          | ~ (v1_funct_2 @ X34 @ X30 @ X32)
% 0.20/0.49          | ~ (v1_funct_1 @ X34)
% 0.20/0.49          | (v1_xboole_0 @ X32))),
% 0.20/0.49      inference('cnf', [status(esa)], [t192_funct_2])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ X1)
% 0.20/0.49          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.20/0.49              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.20/0.49          | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.49          | (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ X1)
% 0.20/0.49          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.20/0.49              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.20/0.49          | (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_B)
% 0.20/0.49          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.20/0.49              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.49          | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.20/0.49  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_B)
% 0.20/0.49          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.20/0.49              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.20/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.20/0.49            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.20/0.49            = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '12'])).
% 0.20/0.49  thf('14', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.49       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.20/0.49          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.20/0.49          | ~ (v1_funct_1 @ X26)
% 0.20/0.49          | (v1_xboole_0 @ X27)
% 0.20/0.49          | ~ (m1_subset_1 @ X29 @ X27)
% 0.20/0.49          | ((k3_funct_2 @ X27 @ X28 @ X26 @ X29) = (k1_funct_1 @ X26 @ X29)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | (v1_xboole_0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.49  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.20/0.49      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.20/0.49            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.20/0.49            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.20/0.49         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.20/0.49         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.20/0.49             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         ((v5_relat_1 @ X15 @ X17)
% 0.20/0.49          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('29', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t2_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ X1)
% 0.20/0.49          | (v1_xboole_0 @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('32', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.20/0.49      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc5_funct_2, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.50             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.50          | (v1_partfun1 @ X18 @ X19)
% 0.20/0.50          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.20/0.50          | ~ (v1_funct_1 @ X18)
% 0.20/0.50          | (v1_xboole_0 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((v1_xboole_0 @ sk_A)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.50        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.20/0.50        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('40', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.50  thf('41', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf(d4_partfun1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.50       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (v1_partfun1 @ X22 @ X21)
% 0.20/0.50          | ((k1_relat_1 @ X22) = (X21))
% 0.20/0.50          | ~ (v4_relat_1 @ X22 @ X21)
% 0.20/0.50          | ~ (v1_relat_1 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.20/0.50        | ~ (v4_relat_1 @ sk_D @ sk_B)
% 0.20/0.50        | ((k1_relat_1 @ sk_D) = (sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( v1_relat_1 @ C ) ))).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((v1_relat_1 @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.50  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X15 @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('50', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.20/0.50  thf(t12_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.50         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.50          | (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ (k2_relat_1 @ X11))
% 0.20/0.50          | ~ (v1_funct_1 @ X11)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.50          | ~ (v1_relat_1 @ sk_D)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.50          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.50          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         ((v5_relat_1 @ X15 @ X17)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('60', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf(d19_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (v5_relat_1 @ X8 @ X9)
% 0.20/0.50          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('64', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf(t3_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X2 : $i, X4 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((m1_subset_1 @ (k2_relat_1 @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf(t4_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.50          | (m1_subset_1 @ X5 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '68'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ X1)
% 0.20/0.50          | (v1_xboole_0 @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.20/0.50      inference('clc', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (v1_partfun1 @ X22 @ X21)
% 0.20/0.50          | ((k1_relat_1 @ X22) = (X21))
% 0.20/0.50          | ~ (v4_relat_1 @ X22 @ X21)
% 0.20/0.50          | ~ (v1_relat_1 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_E)
% 0.20/0.50        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.20/0.50        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         ((v1_relat_1 @ X12)
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.50  thf('79', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('81', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X15 @ X16)
% 0.20/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('82', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['76', '79', '82'])).
% 0.20/0.50  thf(d8_partfun1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.50           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.20/0.50          | ((k7_partfun1 @ X25 @ X24 @ X23) = (k1_funct_1 @ X24 @ X23))
% 0.20/0.50          | ~ (v1_funct_1 @ X24)
% 0.20/0.50          | ~ (v5_relat_1 @ X24 @ X25)
% 0.20/0.50          | ~ (v1_relat_1 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.20/0.50  thf('85', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50          | ~ (v1_relat_1 @ sk_E)
% 0.20/0.50          | ~ (v5_relat_1 @ sk_E @ X1)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ((k7_partfun1 @ X1 @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.50  thf('86', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.50      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.50  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50          | ~ (v5_relat_1 @ sk_E @ X1)
% 0.20/0.50          | ((k7_partfun1 @ X1 @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.50            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.20/0.50          | ~ (v5_relat_1 @ sk_E @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '88'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.20/0.50         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '89'])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.20/0.50         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.20/0.50         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.20/0.50      inference('demod', [status(thm)], ['25', '26', '90'])).
% 0.20/0.50  thf('92', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['24', '91'])).
% 0.20/0.50  thf('93', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('94', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['92', '93'])).
% 0.20/0.50  thf('95', plain, ($false), inference('demod', [status(thm)], ['0', '94'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

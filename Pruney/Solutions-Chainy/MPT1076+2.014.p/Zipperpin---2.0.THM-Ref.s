%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gIgEdjxBUx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 210 expanded)
%              Number of leaves         :   32 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          : 1039 (4782 expanded)
%              Number of equality atoms :   32 ( 110 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_partfun1 @ X24 @ X25 )
      | ( ( k3_funct_2 @ X23 @ X26 @ ( k8_funct_2 @ X23 @ X25 @ X26 @ X27 @ X24 ) @ X28 )
        = ( k1_funct_1 @ X24 @ ( k3_funct_2 @ X23 @ X25 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ X23 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X23 @ X25 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X25 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ X20 )
      | ( ( k3_funct_2 @ X20 @ X21 @ X19 @ X22 )
        = ( k1_funct_1 @ X19 @ X22 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
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

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( v1_partfun1 @ X11 @ X12 )
      | ~ ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['43','44'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ sk_B )
    | ( ( k1_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['47','50','53'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X3 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X3 @ X2 ) @ X4 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v5_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['48','49'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','59'])).

thf('61',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['34','60'])).

thf('62',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_partfun1 @ X15 @ X14 )
      | ( ( k1_relat_1 @ X15 )
        = X14 )
      | ~ ( v4_relat_1 @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_A )
    | ( ( k1_relat_1 @ sk_E )
      = sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['64','67','70'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( ( k7_partfun1 @ X18 @ X17 @ X16 )
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v5_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X1 @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['65','66'])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_E @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
      | ~ ( v5_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','76'])).

thf('78',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['29','77'])).

thf('79',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['25','26','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['24','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gIgEdjxBUx
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:51:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 53 iterations in 0.028s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.22/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(t193_funct_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.50           ( ![C:$i,D:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.22/0.50                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.22/0.50               ( ![E:$i]:
% 0.22/0.50                 ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.50                     ( m1_subset_1 @
% 0.22/0.50                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.22/0.50                   ( ![F:$i]:
% 0.22/0.50                     ( ( m1_subset_1 @ F @ B ) =>
% 0.22/0.50                       ( ( v1_partfun1 @ E @ A ) =>
% 0.22/0.50                         ( ( k3_funct_2 @
% 0.22/0.50                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.22/0.50                           ( k7_partfun1 @
% 0.22/0.50                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.50              ( ![C:$i,D:$i]:
% 0.22/0.50                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.22/0.50                    ( m1_subset_1 @
% 0.22/0.50                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.22/0.50                  ( ![E:$i]:
% 0.22/0.50                    ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.50                        ( m1_subset_1 @
% 0.22/0.50                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.22/0.50                      ( ![F:$i]:
% 0.22/0.50                        ( ( m1_subset_1 @ F @ B ) =>
% 0.22/0.50                          ( ( v1_partfun1 @ E @ A ) =>
% 0.22/0.50                            ( ( k3_funct_2 @
% 0.22/0.50                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.22/0.50                              ( k7_partfun1 @
% 0.22/0.50                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.22/0.50  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t192_funct_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.50           ( ![C:$i,D:$i]:
% 0.22/0.50             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.22/0.50                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.22/0.50               ( ![E:$i]:
% 0.22/0.50                 ( ( ( v1_funct_1 @ E ) & 
% 0.22/0.50                     ( m1_subset_1 @
% 0.22/0.50                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.22/0.50                   ( ![F:$i]:
% 0.22/0.50                     ( ( m1_subset_1 @ F @ B ) =>
% 0.22/0.50                       ( ( v1_partfun1 @ E @ A ) =>
% 0.22/0.50                         ( ( k3_funct_2 @
% 0.22/0.50                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.22/0.50                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ X23)
% 0.22/0.50          | ~ (v1_funct_1 @ X24)
% 0.22/0.50          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.22/0.50          | ~ (v1_partfun1 @ X24 @ X25)
% 0.22/0.50          | ((k3_funct_2 @ X23 @ X26 @ 
% 0.22/0.50              (k8_funct_2 @ X23 @ X25 @ X26 @ X27 @ X24) @ X28)
% 0.22/0.50              = (k1_funct_1 @ X24 @ (k3_funct_2 @ X23 @ X25 @ X27 @ X28)))
% 0.22/0.50          | ~ (m1_subset_1 @ X28 @ X23)
% 0.22/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 0.22/0.50          | ~ (v1_funct_2 @ X27 @ X23 @ X25)
% 0.22/0.50          | ~ (v1_funct_1 @ X27)
% 0.22/0.50          | (v1_xboole_0 @ X25))),
% 0.22/0.50      inference('cnf', [status(esa)], [t192_funct_2])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ sk_A)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ X1)
% 0.22/0.50          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.22/0.50              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.22/0.50              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.22/0.50          | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.50          | (v1_xboole_0 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ sk_A)
% 0.22/0.50          | ~ (v1_funct_1 @ X0)
% 0.22/0.50          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.22/0.50          | ~ (m1_subset_1 @ X2 @ X1)
% 0.22/0.50          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.22/0.50              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.22/0.50              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.22/0.50          | (v1_xboole_0 @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ sk_B)
% 0.22/0.50          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.22/0.50              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.22/0.50              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.50          | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.50  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ sk_B)
% 0.22/0.50          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.22/0.50              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.22/0.50              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | (v1_xboole_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.22/0.50            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.22/0.50            = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))
% 0.22/0.50        | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '12'])).
% 0.22/0.50  thf('14', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k3_funct_2, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.50         ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.50         ( m1_subset_1 @ D @ A ) ) =>
% 0.22/0.50       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.22/0.50          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.22/0.50          | ~ (v1_funct_1 @ X19)
% 0.22/0.50          | (v1_xboole_0 @ X20)
% 0.22/0.50          | ~ (m1_subset_1 @ X22 @ X20)
% 0.22/0.50          | ((k3_funct_2 @ X20 @ X21 @ X19 @ X22) = (k1_funct_1 @ X19 @ X22)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | (v1_xboole_0 @ sk_B)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.50          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.50  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.22/0.50          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.22/0.50      inference('clc', [status(thm)], ['20', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.22/0.50            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.22/0.50            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.22/0.50        | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['13', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.22/0.50         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.22/0.50         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.22/0.50             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '22'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((v5_relat_1 @ X8 @ X10)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('29', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t2_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ X1)
% 0.22/0.50          | (v1_xboole_0 @ X1)
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.50  thf('32', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('33', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('34', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.22/0.50      inference('clc', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((v5_relat_1 @ X8 @ X10)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('37', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc5_funct_2, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.50             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.22/0.50          | (v1_partfun1 @ X11 @ X12)
% 0.22/0.50          | ~ (v1_funct_2 @ X11 @ X12 @ X13)
% 0.22/0.50          | ~ (v1_funct_1 @ X11)
% 0.22/0.50          | (v1_xboole_0 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_A)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_D)
% 0.22/0.50        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.22/0.50        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.50  thf('41', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('42', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('43', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.50  thf('44', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.22/0.50      inference('clc', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf(d4_partfun1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.50       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (v1_partfun1 @ X15 @ X14)
% 0.22/0.50          | ((k1_relat_1 @ X15) = (X14))
% 0.22/0.50          | ~ (v4_relat_1 @ X15 @ X14)
% 0.22/0.50          | ~ (v1_relat_1 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.22/0.50        | ~ (v4_relat_1 @ sk_D @ sk_B)
% 0.22/0.50        | ((k1_relat_1 @ sk_D) = (sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc1_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( v1_relat_1 @ C ) ))).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         ((v1_relat_1 @ X5)
% 0.22/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.50  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X8 @ X9)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('53', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.50  thf('54', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['47', '50', '53'])).
% 0.22/0.50  thf(t172_funct_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.50           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k1_relat_1 @ X3))
% 0.22/0.50          | (r2_hidden @ (k1_funct_1 @ X3 @ X2) @ X4)
% 0.22/0.50          | ~ (v1_funct_1 @ X3)
% 0.22/0.50          | ~ (v5_relat_1 @ X3 @ X4)
% 0.22/0.50          | ~ (v1_relat_1 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.50          | ~ (v1_relat_1 @ sk_D)
% 0.22/0.50          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.50          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.50  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.50  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.50          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.22/0.50          | (r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ sk_A)
% 0.22/0.50          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['37', '59'])).
% 0.22/0.50  thf('61', plain, ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '60'])).
% 0.22/0.50  thf('62', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (~ (v1_partfun1 @ X15 @ X14)
% 0.22/0.50          | ((k1_relat_1 @ X15) = (X14))
% 0.22/0.50          | ~ (v4_relat_1 @ X15 @ X14)
% 0.22/0.50          | ~ (v1_relat_1 @ X15))),
% 0.22/0.50      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_E)
% 0.22/0.50        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.22/0.50        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.50  thf('65', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.50         ((v1_relat_1 @ X5)
% 0.22/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.50  thf('67', plain, ((v1_relat_1 @ sk_E)),
% 0.22/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X8 @ X9)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('70', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.50  thf('71', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['64', '67', '70'])).
% 0.22/0.50  thf(d8_partfun1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.50       ( ![C:$i]:
% 0.22/0.50         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.50           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.22/0.50  thf('72', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.22/0.50          | ((k7_partfun1 @ X18 @ X17 @ X16) = (k1_funct_1 @ X17 @ X16))
% 0.22/0.50          | ~ (v1_funct_1 @ X17)
% 0.22/0.50          | ~ (v5_relat_1 @ X17 @ X18)
% 0.22/0.50          | ~ (v1_relat_1 @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.22/0.50  thf('73', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.50          | ~ (v1_relat_1 @ sk_E)
% 0.22/0.50          | ~ (v5_relat_1 @ sk_E @ X1)
% 0.22/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.22/0.50          | ((k7_partfun1 @ X1 @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.50  thf('74', plain, ((v1_relat_1 @ sk_E)),
% 0.22/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.50  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('76', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.50          | ~ (v5_relat_1 @ sk_E @ X1)
% 0.22/0.50          | ((k7_partfun1 @ X1 @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.22/0.50  thf('77', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.22/0.50            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.22/0.50          | ~ (v5_relat_1 @ sk_E @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['61', '76'])).
% 0.22/0.50  thf('78', plain,
% 0.22/0.50      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.22/0.50         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '77'])).
% 0.22/0.50  thf('79', plain,
% 0.22/0.50      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.22/0.50         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.22/0.50         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.22/0.50      inference('demod', [status(thm)], ['25', '26', '78'])).
% 0.22/0.50  thf('80', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['24', '79'])).
% 0.22/0.50  thf('81', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('82', plain, ((v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('clc', [status(thm)], ['80', '81'])).
% 0.22/0.50  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

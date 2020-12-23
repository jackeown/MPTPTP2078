%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6amRTJbdci

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 260 expanded)
%              Number of leaves         :   24 (  84 expanded)
%              Depth                    :   15
%              Number of atoms          : 1103 (6945 expanded)
%              Number of equality atoms :   34 ( 159 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_partfun1 @ X19 @ X20 )
      | ( ( k3_funct_2 @ X18 @ X21 @ ( k8_funct_2 @ X18 @ X20 @ X21 @ X22 @ X19 ) @ X23 )
        = ( k1_funct_1 @ X19 @ ( k3_funct_2 @ X18 @ X20 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X23 @ X18 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X18 @ X20 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X20 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ X8 )
      | ( ( k3_funct_2 @ X8 @ X9 @ X7 @ X10 )
        = ( k1_funct_1 @ X7 @ X10 ) ) ) ),
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
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X6 @ X4 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X4 @ X5 @ X3 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t176_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X16 )
      | ( ( k7_partfun1 @ X14 @ X17 @ X15 )
        = ( k3_funct_2 @ X16 @ X14 @ X17 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t131_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X11 @ X12 )
      | ( v1_funct_2 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t131_funct_2])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_partfun1 @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('54',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['51','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ X8 )
      | ( ( k3_funct_2 @ X8 @ X9 @ X7 @ X10 )
        = ( k1_funct_1 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['61','71'])).

thf('73',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['24','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6amRTJbdci
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 46 iterations in 0.028s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.21/0.49  thf(t193_funct_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49           ( ![C:$i,D:$i]:
% 0.21/0.49             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.49                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.49               ( ![E:$i]:
% 0.21/0.49                 ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                     ( m1_subset_1 @
% 0.21/0.49                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.49                   ( ![F:$i]:
% 0.21/0.49                     ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.49                       ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.49                         ( ( k3_funct_2 @
% 0.21/0.49                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.49                           ( k7_partfun1 @
% 0.21/0.49                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49              ( ![C:$i,D:$i]:
% 0.21/0.49                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.49                    ( m1_subset_1 @
% 0.21/0.49                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.49                  ( ![E:$i]:
% 0.21/0.49                    ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                        ( m1_subset_1 @
% 0.21/0.49                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.49                      ( ![F:$i]:
% 0.21/0.49                        ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.49                          ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.49                            ( ( k3_funct_2 @
% 0.21/0.49                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.49                              ( k7_partfun1 @
% 0.21/0.49                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.21/0.49  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t192_funct_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49           ( ![C:$i,D:$i]:
% 0.21/0.49             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.49                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.49               ( ![E:$i]:
% 0.21/0.49                 ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                     ( m1_subset_1 @
% 0.21/0.49                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.49                   ( ![F:$i]:
% 0.21/0.49                     ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.49                       ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.49                         ( ( k3_funct_2 @
% 0.21/0.49                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.49                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X18)
% 0.21/0.49          | ~ (v1_funct_1 @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.21/0.49          | ~ (v1_partfun1 @ X19 @ X20)
% 0.21/0.49          | ((k3_funct_2 @ X18 @ X21 @ 
% 0.21/0.49              (k8_funct_2 @ X18 @ X20 @ X21 @ X22 @ X19) @ X23)
% 0.21/0.49              = (k1_funct_1 @ X19 @ (k3_funct_2 @ X18 @ X20 @ X22 @ X23)))
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X20)))
% 0.21/0.49          | ~ (v1_funct_2 @ X22 @ X18 @ X20)
% 0.21/0.49          | ~ (v1_funct_1 @ X22)
% 0.21/0.49          | (v1_xboole_0 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [t192_funct_2])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ X1)
% 0.21/0.49          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.21/0.49              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.21/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.21/0.49          | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ X1)
% 0.21/0.49          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.21/0.49              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.21/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.21/0.49          | (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ sk_B)
% 0.21/0.49          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.49              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.49          | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.49  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ sk_B)
% 0.21/0.49          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.49              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.49              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_A)
% 0.21/0.49        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.49            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.49            = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))
% 0.21/0.49        | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '12'])).
% 0.21/0.49  thf('14', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.49       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.49          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | (v1_xboole_0 @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ X8)
% 0.21/0.49          | ((k3_funct_2 @ X8 @ X9 @ X7 @ X10) = (k1_funct_1 @ X7 @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | (v1_xboole_0 @ sk_B)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.49  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_A)
% 0.21/0.49        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.49            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.49            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.49        | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.49         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.49         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.21/0.49             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.49         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.49         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_k3_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.49       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.21/0.49          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.21/0.49          | ~ (v1_funct_1 @ X3)
% 0.21/0.49          | (v1_xboole_0 @ X4)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ X4)
% 0.21/0.49          | (m1_subset_1 @ (k3_funct_2 @ X4 @ X5 @ X3 @ X6) @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | (v1_xboole_0 @ sk_B)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.49  thf('35', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.49  thf('39', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t176_funct_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.49                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.21/0.49                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X14)
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ X16)
% 0.21/0.49          | ((k7_partfun1 @ X14 @ X17 @ X15)
% 0.21/0.49              = (k3_funct_2 @ X16 @ X14 @ X17 @ X15))
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 0.21/0.49          | ~ (v1_funct_2 @ X17 @ X16 @ X14)
% 0.21/0.49          | ~ (v1_funct_1 @ X17)
% 0.21/0.49          | (v1_xboole_0 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.21/0.49          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.49              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t131_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ( v1_partfun1 @ C @ A ) =>
% 0.21/0.49         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.49         (~ (v1_partfun1 @ X11 @ X12)
% 0.21/0.49          | (v1_funct_2 @ X11 @ X12 @ X13)
% 0.21/0.49          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.21/0.49          | ~ (v1_funct_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t131_funct_2])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((~ (v1_funct_1 @ sk_E)
% 0.21/0.49        | (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.21/0.49        | ~ (v1_partfun1 @ sk_E @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('49', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ sk_A)
% 0.21/0.49          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.49              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['42', '43', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_C)
% 0.21/0.49        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.49            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.49        | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_partfun1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ X1)
% 0.21/0.49          | ~ (v1_partfun1 @ X2 @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.49        | ~ (v1_xboole_0 @ sk_C)
% 0.21/0.49        | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('58', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.49      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_A)
% 0.21/0.49        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.49            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.49      inference('clc', [status(thm)], ['51', '58'])).
% 0.21/0.49  thf('60', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.49         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.49      inference('clc', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.49          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | (v1_xboole_0 @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X10 @ X8)
% 0.21/0.49          | ((k3_funct_2 @ X8 @ X9 @ X7 @ X10) = (k1_funct_1 @ X7 @ X10)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.21/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.49  thf('66', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.21/0.49  thf('69', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.49         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['62', '70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.49         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['61', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.49         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.49         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '72'])).
% 0.21/0.49  thf('74', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['24', '73'])).
% 0.21/0.49  thf('75', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('76', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.49  thf('77', plain, ($false), inference('demod', [status(thm)], ['0', '76'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

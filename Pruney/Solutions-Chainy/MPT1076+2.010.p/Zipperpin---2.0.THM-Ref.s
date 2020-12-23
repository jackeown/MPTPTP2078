%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oJk2BIIVcy

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:29 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 361 expanded)
%              Number of leaves         :   42 ( 121 expanded)
%              Depth                    :   18
%              Number of atoms          : 1350 (8480 expanded)
%              Number of equality atoms :   58 ( 221 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_partfun1 @ X35 @ X36 )
      | ( ( k3_funct_2 @ X34 @ X37 @ ( k8_funct_2 @ X34 @ X36 @ X37 @ X38 @ X35 ) @ X39 )
        = ( k1_funct_1 @ X35 @ ( k3_funct_2 @ X34 @ X36 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X39 @ X34 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X34 @ X36 )
      | ~ ( v1_funct_1 @ X38 )
      | ( v1_xboole_0 @ X36 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ X23 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X23 @ X24 @ X22 @ X25 ) @ X24 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X32 )
      | ( ( k7_partfun1 @ X30 @ X33 @ X31 )
        = ( k3_funct_2 @ X32 @ X30 @ X33 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X32 ) ) ),
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

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('46',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_A )
    | ( ( k1_relat_1 @ sk_E )
      = sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v4_relat_1 @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['46','56'])).

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

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X14
       != ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
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

thf('61',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('67',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( v1_partfun1 @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('68',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['62','73'])).

thf('75',plain,
    ( ( sk_A != sk_A )
    | ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['59','74'])).

thf('76',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('84',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ X27 )
      | ( ( k3_funct_2 @ X27 @ X28 @ X26 @ X29 )
        = ( k1_funct_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['75'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['82','92'])).

thf('94',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['24','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['0','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oJk2BIIVcy
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.64/0.81  % Solved by: fo/fo7.sh
% 0.64/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.81  % done 385 iterations in 0.363s
% 0.64/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.64/0.81  % SZS output start Refutation
% 0.64/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.64/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.64/0.81  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.64/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.64/0.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.64/0.81  thf(sk_F_type, type, sk_F: $i).
% 0.64/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.81  thf(sk_E_type, type, sk_E: $i).
% 0.64/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.64/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.64/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.64/0.81  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.64/0.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.64/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.64/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.64/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.64/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.64/0.81  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.64/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.81  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.64/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.64/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.64/0.81  thf(t193_funct_2, conjecture,
% 0.64/0.81    (![A:$i]:
% 0.64/0.81     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.81       ( ![B:$i]:
% 0.64/0.81         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.64/0.81           ( ![C:$i,D:$i]:
% 0.64/0.81             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.64/0.81                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.64/0.81               ( ![E:$i]:
% 0.64/0.81                 ( ( ( v1_funct_1 @ E ) & 
% 0.64/0.81                     ( m1_subset_1 @
% 0.64/0.81                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.64/0.81                   ( ![F:$i]:
% 0.64/0.81                     ( ( m1_subset_1 @ F @ B ) =>
% 0.64/0.81                       ( ( v1_partfun1 @ E @ A ) =>
% 0.64/0.81                         ( ( k3_funct_2 @
% 0.64/0.81                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.64/0.81                           ( k7_partfun1 @
% 0.64/0.81                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.81    (~( ![A:$i]:
% 0.64/0.81        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.81          ( ![B:$i]:
% 0.64/0.81            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.64/0.81              ( ![C:$i,D:$i]:
% 0.64/0.81                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.64/0.81                    ( m1_subset_1 @
% 0.64/0.81                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.64/0.81                  ( ![E:$i]:
% 0.64/0.81                    ( ( ( v1_funct_1 @ E ) & 
% 0.64/0.81                        ( m1_subset_1 @
% 0.64/0.81                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.64/0.81                      ( ![F:$i]:
% 0.64/0.81                        ( ( m1_subset_1 @ F @ B ) =>
% 0.64/0.81                          ( ( v1_partfun1 @ E @ A ) =>
% 0.64/0.81                            ( ( k3_funct_2 @
% 0.64/0.81                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.64/0.81                              ( k7_partfun1 @
% 0.64/0.81                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.64/0.81    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.64/0.81  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('2', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('3', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(t192_funct_2, axiom,
% 0.64/0.81    (![A:$i]:
% 0.64/0.81     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.81       ( ![B:$i]:
% 0.64/0.81         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.64/0.81           ( ![C:$i,D:$i]:
% 0.64/0.81             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.64/0.81                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.64/0.81               ( ![E:$i]:
% 0.64/0.81                 ( ( ( v1_funct_1 @ E ) & 
% 0.64/0.81                     ( m1_subset_1 @
% 0.64/0.81                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.64/0.81                   ( ![F:$i]:
% 0.64/0.81                     ( ( m1_subset_1 @ F @ B ) =>
% 0.64/0.81                       ( ( v1_partfun1 @ E @ A ) =>
% 0.64/0.81                         ( ( k3_funct_2 @
% 0.64/0.81                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.64/0.81                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.64/0.81  thf('4', plain,
% 0.64/0.81      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ X34)
% 0.64/0.81          | ~ (v1_funct_1 @ X35)
% 0.64/0.81          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.64/0.81          | ~ (v1_partfun1 @ X35 @ X36)
% 0.64/0.81          | ((k3_funct_2 @ X34 @ X37 @ 
% 0.64/0.81              (k8_funct_2 @ X34 @ X36 @ X37 @ X38 @ X35) @ X39)
% 0.64/0.81              = (k1_funct_1 @ X35 @ (k3_funct_2 @ X34 @ X36 @ X38 @ X39)))
% 0.64/0.81          | ~ (m1_subset_1 @ X39 @ X34)
% 0.64/0.81          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X36)))
% 0.64/0.81          | ~ (v1_funct_2 @ X38 @ X34 @ X36)
% 0.64/0.81          | ~ (v1_funct_1 @ X38)
% 0.64/0.81          | (v1_xboole_0 @ X36))),
% 0.64/0.81      inference('cnf', [status(esa)], [t192_funct_2])).
% 0.64/0.81  thf('5', plain,
% 0.64/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ sk_A)
% 0.64/0.81          | ~ (v1_funct_1 @ X0)
% 0.64/0.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.64/0.81          | ~ (m1_subset_1 @ X2 @ X1)
% 0.64/0.81          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.64/0.81              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.64/0.81              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.64/0.81          | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.64/0.81          | ~ (v1_funct_1 @ sk_E)
% 0.64/0.81          | (v1_xboole_0 @ X1))),
% 0.64/0.81      inference('sup-', [status(thm)], ['3', '4'])).
% 0.64/0.81  thf('6', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('8', plain,
% 0.64/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ sk_A)
% 0.64/0.81          | ~ (v1_funct_1 @ X0)
% 0.64/0.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.64/0.81          | ~ (m1_subset_1 @ X2 @ X1)
% 0.64/0.81          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.64/0.81              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.64/0.81              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.64/0.81          | (v1_xboole_0 @ X1))),
% 0.64/0.81      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.64/0.81  thf('9', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ sk_B)
% 0.64/0.81          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.64/0.81              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.64/0.81              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.64/0.81          | ~ (v1_funct_1 @ sk_D)
% 0.64/0.81          | (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['2', '8'])).
% 0.64/0.81  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('12', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ sk_B)
% 0.64/0.81          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.64/0.81              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.64/0.81              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.64/0.81  thf('13', plain,
% 0.64/0.81      (((v1_xboole_0 @ sk_A)
% 0.64/0.81        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.64/0.81            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.64/0.81            = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))
% 0.64/0.81        | (v1_xboole_0 @ sk_B))),
% 0.64/0.81      inference('sup-', [status(thm)], ['1', '12'])).
% 0.64/0.81  thf('14', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('15', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(redefinition_k3_funct_2, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.64/0.81         ( v1_funct_2 @ C @ A @ B ) & 
% 0.64/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.64/0.81         ( m1_subset_1 @ D @ A ) ) =>
% 0.64/0.81       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.64/0.81  thf('16', plain,
% 0.64/0.81      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.64/0.81          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.64/0.81          | ~ (v1_funct_1 @ X26)
% 0.64/0.81          | (v1_xboole_0 @ X27)
% 0.64/0.81          | ~ (m1_subset_1 @ X29 @ X27)
% 0.64/0.81          | ((k3_funct_2 @ X27 @ X28 @ X26 @ X29) = (k1_funct_1 @ X26 @ X29)))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.64/0.81  thf('17', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | (v1_xboole_0 @ sk_B)
% 0.64/0.81          | ~ (v1_funct_1 @ sk_D)
% 0.64/0.81          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.64/0.81  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('20', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | (v1_xboole_0 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.64/0.81  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('22', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.64/0.81      inference('clc', [status(thm)], ['20', '21'])).
% 0.64/0.81  thf('23', plain,
% 0.64/0.81      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.64/0.81      inference('sup-', [status(thm)], ['14', '22'])).
% 0.64/0.81  thf('24', plain,
% 0.64/0.81      (((v1_xboole_0 @ sk_A)
% 0.64/0.81        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.64/0.81            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.64/0.81            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.64/0.81        | (v1_xboole_0 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['13', '23'])).
% 0.64/0.81  thf('25', plain,
% 0.64/0.81      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.64/0.81         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.64/0.81         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.64/0.81             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('26', plain,
% 0.64/0.81      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.64/0.81      inference('sup-', [status(thm)], ['14', '22'])).
% 0.64/0.81  thf('27', plain,
% 0.64/0.81      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.64/0.81         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.64/0.81         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.64/0.81      inference('demod', [status(thm)], ['25', '26'])).
% 0.64/0.81  thf('28', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('29', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(dt_k3_funct_2, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.64/0.81         ( v1_funct_2 @ C @ A @ B ) & 
% 0.64/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.64/0.81         ( m1_subset_1 @ D @ A ) ) =>
% 0.64/0.81       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.64/0.81  thf('30', plain,
% 0.64/0.81      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.64/0.81          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.64/0.81          | ~ (v1_funct_1 @ X22)
% 0.64/0.81          | (v1_xboole_0 @ X23)
% 0.64/0.81          | ~ (m1_subset_1 @ X25 @ X23)
% 0.64/0.81          | (m1_subset_1 @ (k3_funct_2 @ X23 @ X24 @ X22 @ X25) @ X24))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.64/0.81  thf('31', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | (v1_xboole_0 @ sk_B)
% 0.64/0.81          | ~ (v1_funct_1 @ sk_D)
% 0.64/0.81          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['29', '30'])).
% 0.64/0.81  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('33', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('34', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A)
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | (v1_xboole_0 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.64/0.81  thf('35', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('36', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.64/0.81          | (m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) @ sk_A))),
% 0.64/0.81      inference('clc', [status(thm)], ['34', '35'])).
% 0.64/0.81  thf('37', plain,
% 0.64/0.81      ((m1_subset_1 @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) @ sk_A)),
% 0.64/0.81      inference('sup-', [status(thm)], ['28', '36'])).
% 0.64/0.81  thf('38', plain,
% 0.64/0.81      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.64/0.81      inference('sup-', [status(thm)], ['14', '22'])).
% 0.64/0.81  thf('39', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['37', '38'])).
% 0.64/0.81  thf('40', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(t176_funct_2, axiom,
% 0.64/0.81    (![A:$i]:
% 0.64/0.81     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.64/0.81       ( ![B:$i]:
% 0.64/0.81         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.64/0.81           ( ![C:$i]:
% 0.64/0.81             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.64/0.81                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.64/0.81               ( ![D:$i]:
% 0.64/0.81                 ( ( m1_subset_1 @ D @ A ) =>
% 0.64/0.81                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.64/0.81                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.64/0.81  thf('41', plain,
% 0.64/0.81      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ X30)
% 0.64/0.81          | ~ (m1_subset_1 @ X31 @ X32)
% 0.64/0.81          | ((k7_partfun1 @ X30 @ X33 @ X31)
% 0.64/0.81              = (k3_funct_2 @ X32 @ X30 @ X33 @ X31))
% 0.64/0.81          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.64/0.81          | ~ (v1_funct_2 @ X33 @ X32 @ X30)
% 0.64/0.81          | ~ (v1_funct_1 @ X33)
% 0.64/0.81          | (v1_xboole_0 @ X32))),
% 0.64/0.81      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.64/0.81  thf('42', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ sk_A)
% 0.64/0.81          | ~ (v1_funct_1 @ sk_E)
% 0.64/0.81          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.64/0.81          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.64/0.81              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.64/0.81          | (v1_xboole_0 @ sk_C))),
% 0.64/0.81      inference('sup-', [status(thm)], ['40', '41'])).
% 0.64/0.81  thf('43', plain, ((v1_funct_1 @ sk_E)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('44', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(redefinition_k1_relset_1, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.64/0.81  thf('45', plain,
% 0.64/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.64/0.81         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.64/0.81          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.64/0.81  thf('46', plain,
% 0.64/0.81      (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.64/0.81      inference('sup-', [status(thm)], ['44', '45'])).
% 0.64/0.81  thf('47', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(d4_partfun1, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.64/0.81       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.64/0.81  thf('48', plain,
% 0.64/0.81      (![X20 : $i, X21 : $i]:
% 0.64/0.81         (~ (v1_partfun1 @ X21 @ X20)
% 0.64/0.81          | ((k1_relat_1 @ X21) = (X20))
% 0.64/0.81          | ~ (v4_relat_1 @ X21 @ X20)
% 0.64/0.81          | ~ (v1_relat_1 @ X21))),
% 0.64/0.81      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.64/0.81  thf('49', plain,
% 0.64/0.81      ((~ (v1_relat_1 @ sk_E)
% 0.64/0.81        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.64/0.81        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['47', '48'])).
% 0.64/0.81  thf('50', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(cc1_relset_1, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.81       ( v1_relat_1 @ C ) ))).
% 0.64/0.81  thf('51', plain,
% 0.64/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.81         ((v1_relat_1 @ X0)
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2))))),
% 0.64/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.64/0.81  thf('52', plain, ((v1_relat_1 @ sk_E)),
% 0.64/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.64/0.81  thf('53', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(cc2_relset_1, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.64/0.81  thf('54', plain,
% 0.64/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.64/0.81         ((v4_relat_1 @ X3 @ X4)
% 0.64/0.81          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.64/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.64/0.81  thf('55', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.64/0.81      inference('sup-', [status(thm)], ['53', '54'])).
% 0.64/0.81  thf('56', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['49', '52', '55'])).
% 0.64/0.81  thf('57', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['46', '56'])).
% 0.64/0.81  thf(d1_funct_2, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.64/0.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.64/0.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.64/0.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.64/0.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.64/0.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.64/0.81  thf(zf_stmt_1, axiom,
% 0.64/0.81    (![C:$i,B:$i,A:$i]:
% 0.64/0.81     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.64/0.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.64/0.81  thf('58', plain,
% 0.64/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.81         (((X14) != (k1_relset_1 @ X14 @ X15 @ X16))
% 0.64/0.81          | (v1_funct_2 @ X16 @ X14 @ X15)
% 0.64/0.81          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.64/0.81  thf('59', plain,
% 0.64/0.81      ((((sk_A) != (sk_A))
% 0.64/0.81        | ~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_A)
% 0.64/0.81        | (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.64/0.81      inference('sup-', [status(thm)], ['57', '58'])).
% 0.64/0.81  thf('60', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.64/0.81  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.64/0.81  thf(zf_stmt_4, axiom,
% 0.64/0.81    (![B:$i,A:$i]:
% 0.64/0.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.64/0.81       ( zip_tseitin_0 @ B @ A ) ))).
% 0.64/0.81  thf(zf_stmt_5, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i]:
% 0.64/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.81       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.64/0.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.64/0.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.64/0.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.64/0.81  thf('61', plain,
% 0.64/0.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.64/0.81         (~ (zip_tseitin_0 @ X17 @ X18)
% 0.64/0.81          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 0.64/0.81          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.64/0.81  thf('62', plain,
% 0.64/0.81      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['60', '61'])).
% 0.64/0.81  thf('63', plain,
% 0.64/0.81      (![X12 : $i, X13 : $i]:
% 0.64/0.81         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.64/0.81  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.64/0.81  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.64/0.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.64/0.81  thf('65', plain,
% 0.64/0.81      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.64/0.81      inference('sup+', [status(thm)], ['63', '64'])).
% 0.64/0.81  thf('66', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(cc2_partfun1, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.64/0.81       ( ![C:$i]:
% 0.64/0.81         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.81           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.64/0.81  thf('67', plain,
% 0.64/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ X9)
% 0.64/0.81          | ~ (v1_xboole_0 @ X10)
% 0.64/0.81          | ~ (v1_partfun1 @ X11 @ X9)
% 0.64/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.64/0.81      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.64/0.81  thf('68', plain,
% 0.64/0.81      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.64/0.81        | ~ (v1_xboole_0 @ sk_C)
% 0.64/0.81        | (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['66', '67'])).
% 0.64/0.81  thf('69', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('70', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['68', '69'])).
% 0.64/0.81  thf('71', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('72', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.64/0.81      inference('clc', [status(thm)], ['70', '71'])).
% 0.64/0.81  thf('73', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.64/0.81      inference('sup-', [status(thm)], ['65', '72'])).
% 0.64/0.81  thf('74', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['62', '73'])).
% 0.64/0.81  thf('75', plain, ((((sk_A) != (sk_A)) | (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.64/0.81      inference('demod', [status(thm)], ['59', '74'])).
% 0.64/0.81  thf('76', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.64/0.81      inference('simplify', [status(thm)], ['75'])).
% 0.64/0.81  thf('77', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         ((v1_xboole_0 @ sk_A)
% 0.64/0.81          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.64/0.81              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.64/0.81          | (v1_xboole_0 @ sk_C))),
% 0.64/0.81      inference('demod', [status(thm)], ['42', '43', '76'])).
% 0.64/0.81  thf('78', plain,
% 0.64/0.81      (((v1_xboole_0 @ sk_C)
% 0.64/0.81        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.64/0.81            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.64/0.81        | (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['39', '77'])).
% 0.64/0.81  thf('79', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.64/0.81      inference('clc', [status(thm)], ['70', '71'])).
% 0.64/0.81  thf('80', plain,
% 0.64/0.81      (((v1_xboole_0 @ sk_A)
% 0.64/0.81        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.64/0.81            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.64/0.81      inference('clc', [status(thm)], ['78', '79'])).
% 0.64/0.81  thf('81', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('82', plain,
% 0.64/0.81      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.64/0.81         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.64/0.81      inference('clc', [status(thm)], ['80', '81'])).
% 0.64/0.81  thf('83', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['37', '38'])).
% 0.64/0.81  thf('84', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('85', plain,
% 0.64/0.81      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.64/0.81          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.64/0.81          | ~ (v1_funct_1 @ X26)
% 0.64/0.81          | (v1_xboole_0 @ X27)
% 0.64/0.81          | ~ (m1_subset_1 @ X29 @ X27)
% 0.64/0.81          | ((k3_funct_2 @ X27 @ X28 @ X26 @ X29) = (k1_funct_1 @ X26 @ X29)))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.64/0.81  thf('86', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.64/0.81          | (v1_xboole_0 @ sk_A)
% 0.64/0.81          | ~ (v1_funct_1 @ sk_E)
% 0.64/0.81          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.64/0.81      inference('sup-', [status(thm)], ['84', '85'])).
% 0.64/0.81  thf('87', plain, ((v1_funct_1 @ sk_E)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('88', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.64/0.81      inference('simplify', [status(thm)], ['75'])).
% 0.64/0.81  thf('89', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.64/0.81          | (v1_xboole_0 @ sk_A))),
% 0.64/0.81      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.64/0.81  thf('90', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('91', plain,
% 0.64/0.81      (![X0 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.64/0.81          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.64/0.81      inference('clc', [status(thm)], ['89', '90'])).
% 0.64/0.81  thf('92', plain,
% 0.64/0.81      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.64/0.81         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['83', '91'])).
% 0.64/0.81  thf('93', plain,
% 0.64/0.81      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.64/0.81         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.64/0.81      inference('sup+', [status(thm)], ['82', '92'])).
% 0.64/0.81  thf('94', plain,
% 0.64/0.81      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.64/0.81         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.64/0.81         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.64/0.81      inference('demod', [status(thm)], ['27', '93'])).
% 0.64/0.81  thf('95', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.64/0.81      inference('simplify_reflect-', [status(thm)], ['24', '94'])).
% 0.64/0.81  thf('96', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('97', plain, ((v1_xboole_0 @ sk_B)),
% 0.64/0.81      inference('clc', [status(thm)], ['95', '96'])).
% 0.64/0.81  thf('98', plain, ($false), inference('demod', [status(thm)], ['0', '97'])).
% 0.64/0.81  
% 0.64/0.81  % SZS output end Refutation
% 0.64/0.81  
% 0.64/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

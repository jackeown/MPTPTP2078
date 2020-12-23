%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jmDrA665Od

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 319 expanded)
%              Number of leaves         :   35 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          : 1267 (7335 expanded)
%              Number of equality atoms :   37 ( 159 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_partfun1 @ X32 @ X33 )
      | ( ( k3_funct_2 @ X31 @ X34 @ ( k8_funct_2 @ X31 @ X33 @ X34 @ X35 @ X32 ) @ X36 )
        = ( k1_funct_1 @ X32 @ ( k3_funct_2 @ X31 @ X33 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X36 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X31 @ X33 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X33 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ X24 )
      | ( ( k3_funct_2 @ X24 @ X25 @ X23 @ X26 )
        = ( k1_funct_1 @ X23 @ X26 ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('30',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
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
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( v1_partfun1 @ X18 @ X19 )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['41','42'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_partfun1 @ X22 @ X21 )
      | ( ( k1_relat_1 @ X22 )
        = X21 )
      | ~ ( v4_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ sk_B )
    | ( ( k1_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('50',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('53',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['45','50','53'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X7 @ X6 ) @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['48','49'])).

thf('58',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['30','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X29 )
      | ( ( k7_partfun1 @ X27 @ X30 @ X28 )
        = ( k3_funct_2 @ X29 @ X27 @ X30 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('67',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_partfun1 @ X12 @ X13 )
      | ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('68',plain,
    ( ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['64','65','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('75',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( v1_partfun1 @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('76',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['73','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['30','60'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ X24 )
      | ( ( k3_funct_2 @ X24 @ X25 @ X23 @ X26 )
        = ( k1_funct_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['84','92'])).

thf('94',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['83','93'])).

thf('95',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['27','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['24','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['0','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jmDrA665Od
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 66 iterations in 0.020s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(t193_funct_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.48           ( ![C:$i,D:$i]:
% 0.21/0.48             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.48                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.48               ( ![E:$i]:
% 0.21/0.48                 ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.48                     ( m1_subset_1 @
% 0.21/0.48                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.48                   ( ![F:$i]:
% 0.21/0.48                     ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.48                       ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.48                         ( ( k3_funct_2 @
% 0.21/0.48                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.48                           ( k7_partfun1 @
% 0.21/0.48                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.48              ( ![C:$i,D:$i]:
% 0.21/0.48                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.48                    ( m1_subset_1 @
% 0.21/0.48                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.48                  ( ![E:$i]:
% 0.21/0.48                    ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.48                        ( m1_subset_1 @
% 0.21/0.48                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.48                      ( ![F:$i]:
% 0.21/0.48                        ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.48                          ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.48                            ( ( k3_funct_2 @
% 0.21/0.48                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.48                              ( k7_partfun1 @
% 0.21/0.48                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.21/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t192_funct_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.48           ( ![C:$i,D:$i]:
% 0.21/0.48             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.21/0.48                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.21/0.48               ( ![E:$i]:
% 0.21/0.48                 ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.48                     ( m1_subset_1 @
% 0.21/0.48                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.21/0.48                   ( ![F:$i]:
% 0.21/0.48                     ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.48                       ( ( v1_partfun1 @ E @ A ) =>
% 0.21/0.48                         ( ( k3_funct_2 @
% 0.21/0.48                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.21/0.48                           ( k1_funct_1 @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X31)
% 0.21/0.48          | ~ (v1_funct_1 @ X32)
% 0.21/0.48          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.21/0.48          | ~ (v1_partfun1 @ X32 @ X33)
% 0.21/0.48          | ((k3_funct_2 @ X31 @ X34 @ 
% 0.21/0.48              (k8_funct_2 @ X31 @ X33 @ X34 @ X35 @ X32) @ X36)
% 0.21/0.48              = (k1_funct_1 @ X32 @ (k3_funct_2 @ X31 @ X33 @ X35 @ X36)))
% 0.21/0.48          | ~ (m1_subset_1 @ X36 @ X31)
% 0.21/0.48          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X33)))
% 0.21/0.48          | ~ (v1_funct_2 @ X35 @ X31 @ X33)
% 0.21/0.48          | ~ (v1_funct_1 @ X35)
% 0.21/0.48          | (v1_xboole_0 @ X33))),
% 0.21/0.48      inference('cnf', [status(esa)], [t192_funct_2])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ sk_A)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ X1)
% 0.21/0.48          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.21/0.48              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.21/0.48              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.21/0.48          | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.48          | (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.48  thf('6', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('7', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ sk_A)
% 0.21/0.48          | ~ (v1_funct_1 @ X0)
% 0.21/0.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ X1)
% 0.21/0.48          | ((k3_funct_2 @ X1 @ sk_C @ 
% 0.21/0.48              (k8_funct_2 @ X1 @ sk_A @ sk_C @ X0 @ sk_E) @ X2)
% 0.21/0.48              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ X1 @ sk_A @ X0 @ X2)))
% 0.21/0.48          | (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ sk_B)
% 0.21/0.48          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.48              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.48              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.48          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.48          | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '8'])).
% 0.21/0.48  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ sk_B)
% 0.21/0.48          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.48              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.21/0.48              = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0)))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.48          | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A)
% 0.21/0.48        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.48            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.48            = (k1_funct_1 @ sk_E @ (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))
% 0.21/0.48        | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '12'])).
% 0.21/0.48  thf('14', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.48         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.48         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.48       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.21/0.48          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.21/0.48          | ~ (v1_funct_1 @ X23)
% 0.21/0.48          | (v1_xboole_0 @ X24)
% 0.21/0.48          | ~ (m1_subset_1 @ X26 @ X24)
% 0.21/0.48          | ((k3_funct_2 @ X24 @ X25 @ X23 @ X26) = (k1_funct_1 @ X23 @ X26)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.48          | (v1_xboole_0 @ sk_B)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.48          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.48          | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.48  thf('21', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.48          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.21/0.48      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A)
% 0.21/0.48        | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.48            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.48            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.48        | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.48         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.48         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.21/0.48             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.48         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.48         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc2_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         ((v5_relat_1 @ X9 @ X11)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.48  thf('30', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t2_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X0 @ X1)
% 0.21/0.48          | (v1_xboole_0 @ X1)
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.48  thf('33', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.21/0.48      inference('clc', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc5_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.48             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.21/0.48          | (v1_partfun1 @ X18 @ X19)
% 0.21/0.48          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.21/0.48          | ~ (v1_funct_1 @ X18)
% 0.21/0.48          | (v1_xboole_0 @ X20))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.48        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.21/0.48        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.48  thf('42', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.21/0.48      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf(d4_partfun1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X21 : $i, X22 : $i]:
% 0.21/0.48         (~ (v1_partfun1 @ X22 @ X21)
% 0.21/0.48          | ((k1_relat_1 @ X22) = (X21))
% 0.21/0.48          | ~ (v4_relat_1 @ X22 @ X21)
% 0.21/0.48          | ~ (v1_relat_1 @ X22))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.48        | ~ (v4_relat_1 @ sk_D @ sk_B)
% 0.21/0.48        | ((k1_relat_1 @ sk_D) = (sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc2_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.21/0.48          | (v1_relat_1 @ X2)
% 0.21/0.48          | ~ (v1_relat_1 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.48  thf(fc6_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.48  thf('50', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         ((v4_relat_1 @ X9 @ X10)
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.48  thf('53', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.21/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.48  thf('54', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['45', '50', '53'])).
% 0.21/0.48  thf(t176_funct_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.21/0.48         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 0.21/0.48          | (m1_subset_1 @ (k1_funct_1 @ X7 @ X6) @ X8)
% 0.21/0.48          | ~ (v1_funct_1 @ X7)
% 0.21/0.48          | ~ (v5_relat_1 @ X7 @ X8)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.48          | ~ (v1_relat_1 @ sk_D)
% 0.21/0.48          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.48          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.48  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('58', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.48          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.21/0.48          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ X0)
% 0.21/0.48          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '59'])).
% 0.21/0.48  thf('61', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '60'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t176_funct_2, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.48                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.48               ( ![D:$i]:
% 0.21/0.48                 ( ( m1_subset_1 @ D @ A ) =>
% 0.21/0.48                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.21/0.48                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X27)
% 0.21/0.48          | ~ (m1_subset_1 @ X28 @ X29)
% 0.21/0.48          | ((k7_partfun1 @ X27 @ X30 @ X28)
% 0.21/0.48              = (k3_funct_2 @ X29 @ X27 @ X30 @ X28))
% 0.21/0.48          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 0.21/0.48          | ~ (v1_funct_2 @ X30 @ X29 @ X27)
% 0.21/0.48          | ~ (v1_funct_1 @ X30)
% 0.21/0.48          | (v1_xboole_0 @ X29))),
% 0.21/0.48      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ sk_A)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.48          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.21/0.48          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.48              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | (v1_xboole_0 @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.48  thf('65', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc1_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.21/0.48         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (v1_funct_1 @ X12)
% 0.21/0.48          | ~ (v1_partfun1 @ X12 @ X13)
% 0.21/0.48          | (v1_funct_2 @ X12 @ X13 @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      (((v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.21/0.48        | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_E))),
% 0.21/0.48      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.48  thf('69', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('70', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('71', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.48  thf('72', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ sk_A)
% 0.21/0.48          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.21/0.48              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | (v1_xboole_0 @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['64', '65', '71'])).
% 0.21/0.48  thf('73', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_C)
% 0.21/0.48        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.48            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['61', '72'])).
% 0.21/0.48  thf('74', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc2_partfun1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.21/0.48  thf('75', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         ((v1_xboole_0 @ X15)
% 0.21/0.48          | ~ (v1_xboole_0 @ X16)
% 0.21/0.48          | ~ (v1_partfun1 @ X17 @ X15)
% 0.21/0.48          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.21/0.48  thf('76', plain,
% 0.21/0.48      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.21/0.48        | ~ (v1_xboole_0 @ sk_C)
% 0.21/0.48        | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.48  thf('77', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('78', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.48  thf('79', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('80', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.48      inference('clc', [status(thm)], ['78', '79'])).
% 0.21/0.48  thf('81', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A)
% 0.21/0.48        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.48            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.21/0.48      inference('clc', [status(thm)], ['73', '80'])).
% 0.21/0.48  thf('82', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('83', plain,
% 0.21/0.48      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.48         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.48      inference('clc', [status(thm)], ['81', '82'])).
% 0.21/0.48  thf('84', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '60'])).
% 0.21/0.48  thf('85', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('86', plain,
% 0.21/0.48      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.21/0.48          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.21/0.48          | ~ (v1_funct_1 @ X23)
% 0.21/0.48          | (v1_xboole_0 @ X24)
% 0.21/0.48          | ~ (m1_subset_1 @ X26 @ X24)
% 0.21/0.48          | ((k3_funct_2 @ X24 @ X25 @ X23 @ X26) = (k1_funct_1 @ X23 @ X26)))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.48  thf('87', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | (v1_xboole_0 @ sk_A)
% 0.21/0.48          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.48          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.48  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('89', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.48  thf('90', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | (v1_xboole_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.21/0.48  thf('91', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('92', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.21/0.48      inference('clc', [status(thm)], ['90', '91'])).
% 0.21/0.48  thf('93', plain,
% 0.21/0.48      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.48         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['84', '92'])).
% 0.21/0.48  thf('94', plain,
% 0.21/0.48      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.21/0.48         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['83', '93'])).
% 0.21/0.48  thf('95', plain,
% 0.21/0.48      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.21/0.48         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.21/0.48         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.21/0.48      inference('demod', [status(thm)], ['27', '94'])).
% 0.21/0.48  thf('96', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['24', '95'])).
% 0.21/0.48  thf('97', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('98', plain, ((v1_xboole_0 @ sk_B)),
% 0.21/0.48      inference('clc', [status(thm)], ['96', '97'])).
% 0.21/0.48  thf('99', plain, ($false), inference('demod', [status(thm)], ['0', '98'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

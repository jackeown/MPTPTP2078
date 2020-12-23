%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0987+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.neh4iFVxaY

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:50 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 275 expanded)
%              Number of leaves         :   31 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  870 (5206 expanded)
%              Number of equality atoms :   26 (  54 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t33_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ A @ B )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ B @ C )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                 => ( ( ( v2_funct_2 @ D @ B )
                      & ( v2_funct_2 @ E @ C ) )
                   => ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ A @ B )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( v1_funct_2 @ E @ B @ C )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                   => ( ( ( v2_funct_2 @ D @ B )
                        & ( v2_funct_2 @ E @ C ) )
                     => ( v2_funct_2 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_funct_2])).

thf('0',plain,(
    ~ ( v2_funct_2 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k1_partfun1 @ X18 @ X19 @ X21 @ X22 @ X17 @ X20 )
        = ( k5_relat_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_E ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_E ) @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_funct_2 @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_2 @ X7 @ X6 )
      | ( ( k2_relat_1 @ X7 )
        = X6 )
      | ~ ( v5_relat_1 @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_B )
    | ( ( k2_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v5_relat_1 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['22','25','28'])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X29 @ X30 ) )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X30 ) @ ( k2_relat_1 @ X29 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['23','24'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
      = ( k2_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    v2_funct_2 @ sk_E @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v2_funct_2 @ X7 @ X6 )
      | ( ( k2_relat_1 @ X7 )
        = X6 )
      | ~ ( v5_relat_1 @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v5_relat_1 @ sk_E @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('40',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v5_relat_1 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['37','40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['38','39'])).

thf('46',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['34','44','45'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ X7 )
       != X6 )
      | ( v2_funct_2 @ X7 @ X6 )
      | ~ ( v5_relat_1 @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('48',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v5_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
      | ( v2_funct_2 @ X7 @ ( k2_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C )
    | ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['34','44','45'])).

thf('51',plain,
    ( ~ ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C )
    | ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X9 @ X10 @ X12 @ X13 @ X8 @ X11 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('64',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C )
    | ( v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ) ),
    inference(demod,[status(thm)],['51','64'])).

thf('66',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('67',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v5_relat_1 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('68',plain,(
    v5_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('70',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    v2_funct_2 @ ( k5_relat_1 @ sk_D @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['10','71'])).


%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HiM6GiV1tK

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:43 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 115 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  730 (2285 expanded)
%              Number of equality atoms :   39 ( 160 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k9_relat_1 @ X4 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k2_relset_1 @ X7 @ X8 @ X6 )
        = ( k2_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['13','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['25','34'])).

thf('36',plain,
    ( ( ( k9_relat_1 @ sk_E @ sk_B )
     != sk_C )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['12','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k7_relset_1 @ X13 @ X14 @ X15 @ X13 )
        = ( k2_relset_1 @ X13 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('39',plain,
    ( ( k7_relset_1 @ sk_B @ sk_C @ sk_E @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_C @ sk_E ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k7_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k9_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_C @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k9_relat_1 @ sk_E @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['39','42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['36','44','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HiM6GiV1tK
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 130 iterations in 0.113s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.57  thf(t20_funct_2, conjecture,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57       ( ![E:$i]:
% 0.37/0.57         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.37/0.57             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.37/0.57           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.37/0.57               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.37/0.57             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57               ( ( k2_relset_1 @
% 0.37/0.57                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.37/0.57                 ( C ) ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.57          ( ![E:$i]:
% 0.37/0.57            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.37/0.57                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.37/0.57              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.37/0.57                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.37/0.57                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.37/0.57                  ( ( k2_relset_1 @
% 0.37/0.57                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.37/0.57                    ( C ) ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 0.37/0.57  thf('0', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.57         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 0.37/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.57  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf('3', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('4', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf(t160_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( v1_relat_1 @ B ) =>
% 0.37/0.57           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.37/0.57             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         (~ (v1_relat_1 @ X4)
% 0.37/0.57          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.37/0.57              = (k9_relat_1 @ X4 @ (k2_relat_1 @ X5)))
% 0.37/0.57          | ~ (v1_relat_1 @ X5))),
% 0.37/0.57      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.37/0.57  thf('6', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ X0 @ sk_B))
% 0.37/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.37/0.57          | ~ (v1_relat_1 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['4', '5'])).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(cc2_relat_1, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( v1_relat_1 @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.57          | (v1_relat_1 @ X0)
% 0.37/0.57          | ~ (v1_relat_1 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.37/0.57  thf(fc6_relat_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.57  thf('11', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('12', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (((k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)) = (k9_relat_1 @ X0 @ sk_B))
% 0.37/0.57          | ~ (v1_relat_1 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['6', '11'])).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.37/0.57         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('14', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(dt_k1_partfun1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.57         ( v1_funct_1 @ F ) & 
% 0.37/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.37/0.57       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.37/0.57         ( m1_subset_1 @
% 0.37/0.57           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.37/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.37/0.57          | ~ (v1_funct_1 @ X16)
% 0.37/0.57          | ~ (v1_funct_1 @ X19)
% 0.37/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.37/0.57          | (m1_subset_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 0.37/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 0.37/0.57      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.37/0.57          | ~ (v1_funct_1 @ X1)
% 0.37/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.37/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.57  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.37/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.37/0.57          | ~ (v1_funct_1 @ X1))),
% 0.37/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.37/0.57        | (m1_subset_1 @ 
% 0.37/0.57           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.37/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '19'])).
% 0.37/0.57  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      ((m1_subset_1 @ 
% 0.37/0.57        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.37/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.37/0.57      inference('demod', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.57         (((k2_relset_1 @ X7 @ X8 @ X6) = (k2_relat_1 @ X6))
% 0.37/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.37/0.57         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 0.37/0.57         = (k2_relat_1 @ 
% 0.37/0.57            (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (((k2_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 0.37/0.57         != (sk_C))),
% 0.37/0.57      inference('demod', [status(thm)], ['13', '24'])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k1_partfun1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.37/0.57     ( ( ( v1_funct_1 @ E ) & 
% 0.37/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.57         ( v1_funct_1 @ F ) & 
% 0.37/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.37/0.57       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.37/0.57          | ~ (v1_funct_1 @ X22)
% 0.37/0.57          | ~ (v1_funct_1 @ X25)
% 0.37/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.37/0.57          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.37/0.57              = (k5_relat_1 @ X22 @ X25)))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.37/0.57            = (k5_relat_1 @ sk_D @ X0))
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.37/0.57          | ~ (v1_funct_1 @ X0)
% 0.37/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.37/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.37/0.57            = (k5_relat_1 @ sk_D @ X0))
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.37/0.57          | ~ (v1_funct_1 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.37/0.57        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.37/0.57            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['26', '31'])).
% 0.37/0.57  thf('33', plain, ((v1_funct_1 @ sk_E)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.37/0.57         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.37/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.37/0.57  thf('35', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 0.37/0.57      inference('demod', [status(thm)], ['25', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      ((((k9_relat_1 @ sk_E @ sk_B) != (sk_C)) | ~ (v1_relat_1 @ sk_E))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '35'])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t38_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.37/0.57         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.57         (((k7_relset_1 @ X13 @ X14 @ X15 @ X13)
% 0.37/0.57            = (k2_relset_1 @ X13 @ X14 @ X15))
% 0.37/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.37/0.57      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((k7_relset_1 @ sk_B @ sk_C @ sk_E @ sk_B)
% 0.37/0.57         = (k2_relset_1 @ sk_B @ sk_C @ sk_E))),
% 0.37/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('40', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.37/0.57          | ((k7_relset_1 @ X10 @ X11 @ X9 @ X12) = (k9_relat_1 @ X9 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k7_relset_1 @ sk_B @ sk_C @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf('43', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('44', plain, (((k9_relat_1 @ sk_E @ sk_B) = (sk_C))),
% 0.37/0.57      inference('demod', [status(thm)], ['39', '42', '43'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('46', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.37/0.57          | (v1_relat_1 @ X0)
% 0.37/0.57          | ~ (v1_relat_1 @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.57  thf('47', plain,
% 0.37/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.37/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('48', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.57  thf('49', plain, ((v1_relat_1 @ sk_E)),
% 0.37/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.37/0.57  thf('50', plain, (((sk_C) != (sk_C))),
% 0.37/0.57      inference('demod', [status(thm)], ['36', '44', '49'])).
% 0.37/0.57  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

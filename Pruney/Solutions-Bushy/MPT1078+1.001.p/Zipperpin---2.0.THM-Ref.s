%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1078+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xKQE3V43lt

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:01 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 850 expanded)
%              Number of leaves         :   35 ( 257 expanded)
%              Depth                    :   15
%              Number of atoms          : 2375 (27281 expanded)
%              Number of equality atoms :   36 ( 120 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t195_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i,D: $i,E: $i,F: $i] :
              ( ( ( v1_funct_1 @ F )
                & ( v1_funct_2 @ F @ A @ B )
                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [G: $i] :
                  ( ( ( v1_funct_1 @ G )
                    & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                 => ( ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ F ) @ ( k1_relset_1 @ B @ C @ ( k2_partfun1 @ B @ C @ G @ D ) ) )
                      & ( r1_tarski @ D @ E ) )
                   => ( r2_funct_2 @ A @ C @ ( k8_funct_2 @ A @ B @ C @ F @ ( k2_partfun1 @ B @ C @ G @ D ) ) @ ( k8_funct_2 @ A @ B @ C @ F @ ( k2_partfun1 @ B @ C @ G @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i,D: $i,E: $i,F: $i] :
                ( ( ( v1_funct_1 @ F )
                  & ( v1_funct_2 @ F @ A @ B )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [G: $i] :
                    ( ( ( v1_funct_1 @ G )
                      & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                   => ( ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ F ) @ ( k1_relset_1 @ B @ C @ ( k2_partfun1 @ B @ C @ G @ D ) ) )
                        & ( r1_tarski @ D @ E ) )
                     => ( r2_funct_2 @ A @ C @ ( k8_funct_2 @ A @ B @ C @ F @ ( k2_partfun1 @ B @ C @ G @ D ) ) @ ( k8_funct_2 @ A @ B @ C @ F @ ( k2_partfun1 @ B @ C @ G @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t195_funct_2])).

thf('0',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_E ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ( ( k2_partfun1 @ X16 @ X17 @ X15 @ X18 )
        = ( k7_relat_1 @ X15 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
        = ( k7_relat_1 @ sk_G @ X0 ) )
      | ~ ( v1_funct_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('7',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_D ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['0','5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_F ) @ ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_F )
    = ( k2_relat_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X4 @ X5 @ X3 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) )
      = ( k1_relat_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relat_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_D ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_F )
    = ( k2_relat_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t194_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i,D: $i,E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( v1_funct_2 @ E @ A @ B )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [F: $i] :
                  ( ( ( v1_funct_1 @ F )
                    & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
                 => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ E ) @ ( k1_relset_1 @ B @ C @ ( k2_partfun1 @ B @ C @ F @ D ) ) )
                   => ( r2_funct_2 @ A @ C @ ( k8_funct_2 @ A @ B @ C @ E @ ( k2_partfun1 @ B @ C @ F @ D ) ) @ ( k8_funct_2 @ A @ B @ C @ E @ F ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X35 ) ) )
      | ( r2_funct_2 @ X36 @ X35 @ ( k8_funct_2 @ X36 @ X33 @ X35 @ X37 @ ( k2_partfun1 @ X33 @ X35 @ X34 @ X38 ) ) @ ( k8_funct_2 @ X36 @ X33 @ X35 @ X37 @ X34 ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X36 @ X33 @ X37 ) @ ( k1_relset_1 @ X33 @ X35 @ ( k2_partfun1 @ X33 @ X35 @ X34 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X33 )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t194_funct_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relset_1 @ sk_B @ X2 @ ( k2_partfun1 @ sk_B @ X2 @ X1 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ( r2_funct_2 @ sk_A @ X2 @ ( k8_funct_2 @ sk_A @ sk_B @ X2 @ sk_F @ ( k2_partfun1 @ sk_B @ X2 @ X1 @ X0 ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ X2 @ sk_F @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_F @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relset_1 @ sk_B @ X2 @ ( k2_partfun1 @ sk_B @ X2 @ X1 @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_funct_2 @ sk_A @ X2 @ ( k8_funct_2 @ sk_A @ sk_B @ X2 @ sk_F @ ( k2_partfun1 @ sk_B @ X2 @ X1 @ X0 ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ X2 @ sk_F @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_G @ X0 ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
      | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) )
      = ( k1_relat_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_G @ X0 ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ X0 ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','35','36','37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_D ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_D ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_D ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('46',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X8 @ X9 @ X11 @ X7 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ X0 @ sk_F @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_F @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ X0 @ sk_F @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X4 @ X5 @ X3 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) )
      | ~ ( v1_funct_1 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_funct_2 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ X1 )
      | ( ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_2 @ X1 @ sk_A @ sk_C )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('64',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X8 @ X9 @ X11 @ X7 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ X1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_F @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ X1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('72',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('74',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('76',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X8 @ X9 @ X11 @ X7 @ X10 ) @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ X0 @ sk_F @ X1 ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_F @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ X0 @ sk_F @ X1 ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('84',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ X1 )
      | ( ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_2 @ X1 @ sk_A @ sk_C )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','74','86'])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
    | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_D ) )
      = ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ) ),
    inference('sup-',[status(thm)],['44','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ X1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('91',plain,
    ( ~ ( v1_funct_1 @ sk_G )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ X0 @ sk_F @ X1 ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_G )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ X0 @ sk_F @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('101',plain,
    ( ~ ( v1_funct_1 @ sk_G )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    v1_funct_1 @ sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_D ) )
    = ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['88','93','98','103'])).

thf('105',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['7','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('110',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    r1_tarski @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('112',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ( r1_tarski @ ( k7_relat_1 @ X32 @ X30 ) @ ( k7_relat_1 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t104_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_D ) @ ( k7_relat_1 @ X0 @ sk_E ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('114',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k1_relat_1 @ X43 ) @ ( k1_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_D ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_D ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_E ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_E ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_D ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_G ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('118',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('120',plain,(
    v1_relat_1 @ sk_G ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_D ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_E ) ) ),
    inference(demod,[status(thm)],['116','117','120'])).

thf('122',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_F ) @ ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('123',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ X39 @ X40 )
      | ~ ( r1_tarski @ X40 @ X41 )
      | ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_F ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_F )
    = ( k2_relat_1 @ sk_F ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ sk_B @ sk_C @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) )
      = ( k1_relat_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ sk_D ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_B @ sk_C @ sk_G @ X0 )
      = ( k7_relat_1 @ sk_G @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_D ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ sk_E ) ) ),
    inference('sup-',[status(thm)],['121','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_F ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_G @ X0 ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','35','36','37','38'])).

thf('133',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_E ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_E ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_E ) ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) ) @ X1 )
      | ( ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ X0 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_2 @ X1 @ sk_A @ sk_C )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['62','74','86'])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
    | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_E ) )
      = ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('141',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['96','97'])).

thf('142',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('143',plain,
    ( ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ ( k7_relat_1 @ sk_G @ sk_E ) )
    = ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['139','140','141','142'])).

thf('144',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('145',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_funct_2 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('146',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_funct_2 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) )
    | ( r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ) ),
    inference('sup-',[status(thm)],['144','146'])).

thf('148',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['96','97'])).

thf('149',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('150',plain,(
    r2_funct_2 @ sk_A @ sk_C @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) @ ( k8_funct_2 @ sk_A @ sk_B @ sk_C @ sk_F @ sk_G ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,(
    $false ),
    inference(demod,[status(thm)],['105','143','150'])).


%------------------------------------------------------------------------------

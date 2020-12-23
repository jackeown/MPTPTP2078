%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exMDd1DtnY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 139 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  920 (2433 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_funct_2_type,type,(
    k6_funct_2: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t184_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                 => ( r1_tarski @ ( k5_setfam_1 @ A @ D ) @ ( k5_setfam_1 @ A @ ( k6_funct_2 @ A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                   => ( r1_tarski @ ( k5_setfam_1 @ A @ D ) @ ( k5_setfam_1 @ A @ ( k6_funct_2 @ A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t184_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_setfam_1 @ sk_A @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k5_setfam_1 @ X7 @ X6 )
        = ( k3_tarski @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_D )
    = ( k3_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ( m1_subset_1 @ ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X18 @ X19 @ X17 @ X20 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) )
     => ( m1_subset_1 @ ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X14 @ X15 @ X13 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k5_setfam_1 @ X7 @ X6 )
        = ( k3_tarski @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    = ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['4','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('33',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_D )
    = ( k3_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t182_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
                     => ( ( m1_setfam_1 @ D @ E )
                       => ( m1_setfam_1 @ ( k6_funct_2 @ A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ E ) ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) )
      | ~ ( m1_setfam_1 @ X22 @ X24 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ X23 @ X21 @ X25 @ ( k7_funct_2 @ X23 @ X21 @ X25 @ X22 ) ) @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X21 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t182_funct_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ X1 @ X0 @ ( k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D ) ) @ X2 )
      | ~ ( m1_setfam_1 @ sk_D @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ~ ( m1_setfam_1 @ sk_D @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k5_setfam_1 @ X11 @ X12 )
       != X11 )
      | ( m1_setfam_1 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) )
      | ( ( k5_setfam_1 @ ( k3_tarski @ X0 ) @ X0 )
       != ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k5_setfam_1 @ X7 @ X6 )
        = ( k3_tarski @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( k3_tarski @ X0 ) @ X0 )
      = ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) )
      | ( ( k3_tarski @ X0 )
       != ( k3_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('60',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X2 ) )
      | ~ ( m1_setfam_1 @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('61',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['30','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.exMDd1DtnY
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 92 iterations in 0.037s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(t184_funct_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49                   ( r1_tarski @
% 0.20/0.49                     ( k5_setfam_1 @ A @ D ) @ 
% 0.20/0.49                     ( k5_setfam_1 @
% 0.20/0.49                       A @ 
% 0.20/0.49                       ( k6_funct_2 @
% 0.20/0.49                         A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49              ( ![C:$i]:
% 0.20/0.49                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49                    ( m1_subset_1 @
% 0.20/0.49                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49                  ( ![D:$i]:
% 0.20/0.49                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49                      ( r1_tarski @
% 0.20/0.49                        ( k5_setfam_1 @ A @ D ) @ 
% 0.20/0.49                        ( k5_setfam_1 @
% 0.20/0.49                          A @ 
% 0.20/0.49                          ( k6_funct_2 @
% 0.20/0.49                            A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t184_funct_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (~ (r1_tarski @ (k5_setfam_1 @ sk_A @ sk_D) @ 
% 0.20/0.49          (k5_setfam_1 @ sk_A @ 
% 0.20/0.49           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k5_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (((k5_setfam_1 @ X7 @ X6) = (k3_tarski @ X6))
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.49  thf('3', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.20/0.49          (k5_setfam_1 @ sk_A @ 
% 0.20/0.49           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k7_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @
% 0.20/0.49         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.20/0.49          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.20/0.49          | ~ (v1_funct_1 @ X17)
% 0.20/0.49          | (v1_xboole_0 @ X19)
% 0.20/0.49          | (v1_xboole_0 @ X18)
% 0.20/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.20/0.49          | (m1_subset_1 @ (k7_funct_2 @ X18 @ X19 @ X17 @ X20) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.49          | (v1_xboole_0 @ sk_A)
% 0.20/0.49          | (v1_xboole_0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.49          | (v1_xboole_0 @ sk_A)
% 0.20/0.49          | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '11'])).
% 0.20/0.49  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.20/0.49      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k6_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.49         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @
% 0.20/0.49         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.49          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | (v1_xboole_0 @ X15)
% 0.20/0.49          | (v1_xboole_0 @ X14)
% 0.20/0.49          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.20/0.49          | (m1_subset_1 @ (k6_funct_2 @ X14 @ X15 @ X13 @ X16) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.20/0.49          | (v1_xboole_0 @ sk_A)
% 0.20/0.49          | (v1_xboole_0 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('21', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.20/0.49          | (v1_xboole_0 @ sk_A)
% 0.20/0.49          | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B)
% 0.20/0.49        | (v1_xboole_0 @ sk_A)
% 0.20/0.49        | (m1_subset_1 @ 
% 0.20/0.49           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '22'])).
% 0.20/0.49  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((m1_subset_1 @ 
% 0.20/0.49         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.49        | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((m1_subset_1 @ 
% 0.20/0.49        (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (((k5_setfam_1 @ X7 @ X6) = (k3_tarski @ X6))
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (((k5_setfam_1 @ sk_A @ 
% 0.20/0.49         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.20/0.49         = (k3_tarski @ 
% 0.20/0.49            (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49             (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.20/0.49          (k3_tarski @ 
% 0.20/0.49           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_k5_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k5_setfam_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.20/0.49          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.49  thf('34', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('35', plain, ((m1_subset_1 @ (k3_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t182_funct_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49               ( ![D:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49                   ( ![E:$i]:
% 0.20/0.49                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49                       ( ( m1_setfam_1 @ D @ E ) =>
% 0.20/0.49                         ( m1_setfam_1 @
% 0.20/0.49                           ( k6_funct_2 @
% 0.20/0.49                             A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ 
% 0.20/0.49                           E ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X21)
% 0.20/0.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23)))
% 0.20/0.49          | ~ (m1_setfam_1 @ X22 @ X24)
% 0.20/0.49          | (m1_setfam_1 @ 
% 0.20/0.49             (k6_funct_2 @ X23 @ X21 @ X25 @ 
% 0.20/0.49              (k7_funct_2 @ X23 @ X21 @ X25 @ X22)) @ 
% 0.20/0.49             X24)
% 0.20/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X21)))
% 0.20/0.49          | ~ (v1_funct_2 @ X25 @ X23 @ X21)
% 0.20/0.49          | ~ (v1_funct_1 @ X25)
% 0.20/0.49          | (v1_xboole_0 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [t182_funct_2])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_2 @ X0 @ sk_A @ X1)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.20/0.49          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49          | (m1_setfam_1 @ 
% 0.20/0.49             (k6_funct_2 @ sk_A @ X1 @ X0 @ 
% 0.20/0.49              (k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D)) @ 
% 0.20/0.49             X2)
% 0.20/0.49          | ~ (m1_setfam_1 @ sk_D @ X2)
% 0.20/0.49          | (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_B)
% 0.20/0.49          | ~ (m1_setfam_1 @ sk_D @ X0)
% 0.20/0.49          | (m1_setfam_1 @ 
% 0.20/0.49             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49              (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.49          | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.49  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_B)
% 0.20/0.49          | ~ (m1_setfam_1 @ sk_D @ X0)
% 0.20/0.49          | (m1_setfam_1 @ 
% 0.20/0.49             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49              (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49             X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.49          | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | (m1_setfam_1 @ 
% 0.20/0.49           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49           (k3_tarski @ sk_D))
% 0.20/0.49        | ~ (m1_setfam_1 @ sk_D @ (k3_tarski @ sk_D))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '43'])).
% 0.20/0.49  thf(t100_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X0 : $i]: (r1_tarski @ X0 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X8 : $i, X10 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf(t60_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.49       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (((k5_setfam_1 @ X11 @ X12) != (X11))
% 0.20/0.49          | (m1_setfam_1 @ X12 @ X11)
% 0.20/0.49          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.49      inference('cnf', [status(esa)], [t60_setfam_1])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_setfam_1 @ X0 @ (k3_tarski @ X0))
% 0.20/0.49          | ((k5_setfam_1 @ (k3_tarski @ X0) @ X0) != (k3_tarski @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (((k5_setfam_1 @ X7 @ X6) = (k3_tarski @ X6))
% 0.20/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X7))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X0 : $i]: ((k5_setfam_1 @ (k3_tarski @ X0) @ X0) = (k3_tarski @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_setfam_1 @ X0 @ (k3_tarski @ X0))
% 0.20/0.49          | ((k3_tarski @ X0) != (k3_tarski @ X0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['49', '52'])).
% 0.20/0.49  thf('54', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['53'])).
% 0.20/0.49  thf('55', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_A)
% 0.20/0.49        | (m1_setfam_1 @ 
% 0.20/0.49           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49           (k3_tarski @ sk_D))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['44', '54'])).
% 0.20/0.49  thf('56', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('57', plain,
% 0.20/0.49      (((v1_xboole_0 @ sk_B)
% 0.20/0.49        | (m1_setfam_1 @ 
% 0.20/0.49           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49           (k3_tarski @ sk_D)))),
% 0.20/0.49      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.49  thf('58', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      ((m1_setfam_1 @ 
% 0.20/0.49        (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.20/0.49        (k3_tarski @ sk_D))),
% 0.20/0.49      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.49  thf(d12_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.49  thf('60', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_tarski @ X1 @ (k3_tarski @ X2)) | ~ (m1_setfam_1 @ X2 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.20/0.49  thf('61', plain,
% 0.20/0.49      ((r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.20/0.49        (k3_tarski @ 
% 0.20/0.49         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.20/0.49          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.49  thf('62', plain, ($false), inference('demod', [status(thm)], ['30', '61'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

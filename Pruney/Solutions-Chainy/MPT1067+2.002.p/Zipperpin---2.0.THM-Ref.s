%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.piBSyFtGRN

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:56 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 127 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  845 (2330 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_funct_2_type,type,(
    k6_funct_2: $i > $i > $i > $i > $i )).

thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

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
    ! [X8: $i,X9: $i] :
      ( ( ( k5_setfam_1 @ X9 @ X8 )
        = ( k3_tarski @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X11 @ X12 @ X10 @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k5_setfam_1 @ X9 @ X8 )
        = ( k3_tarski @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) )
      | ~ ( m1_setfam_1 @ X19 @ X21 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ X20 @ X18 @ X22 @ ( k7_funct_2 @ X20 @ X18 @ X22 @ X19 ) ) @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X18 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X20 ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_setfam_1 @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( m1_setfam_1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('55',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['30','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.piBSyFtGRN
% 0.12/0.36  % Computer   : n019.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 20:36:22 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 45 iterations in 0.038s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.33/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.33/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.33/0.52  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.33/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.33/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.33/0.52  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 0.33/0.52  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 0.33/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.33/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.52  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.33/0.52  thf(t184_funct_2, conjecture,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.52                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.33/0.52               ( ![D:$i]:
% 0.33/0.52                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52                   ( r1_tarski @
% 0.33/0.52                     ( k5_setfam_1 @ A @ D ) @ 
% 0.33/0.52                     ( k5_setfam_1 @
% 0.33/0.52                       A @ 
% 0.33/0.52                       ( k6_funct_2 @
% 0.33/0.52                         A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i]:
% 0.33/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.33/0.52          ( ![B:$i]:
% 0.33/0.52            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.33/0.52              ( ![C:$i]:
% 0.33/0.52                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.52                    ( m1_subset_1 @
% 0.33/0.52                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.33/0.52                  ( ![D:$i]:
% 0.33/0.52                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52                      ( r1_tarski @
% 0.33/0.52                        ( k5_setfam_1 @ A @ D ) @ 
% 0.33/0.52                        ( k5_setfam_1 @
% 0.33/0.52                          A @ 
% 0.33/0.52                          ( k6_funct_2 @
% 0.33/0.52                            A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t184_funct_2])).
% 0.33/0.52  thf('0', plain,
% 0.33/0.52      (~ (r1_tarski @ (k5_setfam_1 @ sk_A @ sk_D) @ 
% 0.33/0.52          (k5_setfam_1 @ sk_A @ 
% 0.33/0.52           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('1', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(redefinition_k5_setfam_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X8 : $i, X9 : $i]:
% 0.33/0.52         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.33/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.33/0.52      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.33/0.52  thf('3', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 0.33/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.52  thf('4', plain,
% 0.33/0.52      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.33/0.52          (k5_setfam_1 @ sk_A @ 
% 0.33/0.52           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.33/0.52      inference('demod', [status(thm)], ['0', '3'])).
% 0.33/0.52  thf('5', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('6', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(dt_k7_funct_2, axiom,
% 0.33/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.33/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.33/0.52         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.33/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.33/0.52       ( m1_subset_1 @
% 0.33/0.52         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 0.33/0.52  thf('7', plain,
% 0.33/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.33/0.52          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.33/0.52          | ~ (v1_funct_1 @ X14)
% 0.33/0.52          | (v1_xboole_0 @ X16)
% 0.33/0.52          | (v1_xboole_0 @ X15)
% 0.33/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.33/0.52          | (m1_subset_1 @ (k7_funct_2 @ X15 @ X16 @ X14 @ X17) @ 
% 0.33/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.33/0.52      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 0.33/0.52  thf('8', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.33/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.33/0.52          | (v1_xboole_0 @ sk_A)
% 0.33/0.52          | (v1_xboole_0 @ sk_B)
% 0.33/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.33/0.52          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.33/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.33/0.52  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.33/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.33/0.52          | (v1_xboole_0 @ sk_A)
% 0.33/0.52          | (v1_xboole_0 @ sk_B))),
% 0.33/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      (((v1_xboole_0 @ sk_B)
% 0.33/0.52        | (v1_xboole_0 @ sk_A)
% 0.33/0.52        | (m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.33/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 0.33/0.52      inference('sup-', [status(thm)], ['5', '11'])).
% 0.33/0.52  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('14', plain,
% 0.33/0.52      (((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.33/0.52         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.33/0.52        | (v1_xboole_0 @ sk_A))),
% 0.33/0.52      inference('clc', [status(thm)], ['12', '13'])).
% 0.33/0.52  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('16', plain,
% 0.33/0.52      ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.33/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.33/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.33/0.52  thf('17', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(dt_k6_funct_2, axiom,
% 0.33/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.33/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.33/0.52         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.33/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 0.33/0.52       ( m1_subset_1 @
% 0.33/0.52         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.33/0.52  thf('18', plain,
% 0.33/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.33/0.52          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.33/0.52          | ~ (v1_funct_1 @ X10)
% 0.33/0.52          | (v1_xboole_0 @ X12)
% 0.33/0.52          | (v1_xboole_0 @ X11)
% 0.33/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12)))
% 0.33/0.52          | (m1_subset_1 @ (k6_funct_2 @ X11 @ X12 @ X10 @ X13) @ 
% 0.33/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.33/0.52      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 0.33/0.52  thf('19', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.33/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.33/0.52          | (v1_xboole_0 @ sk_A)
% 0.33/0.52          | (v1_xboole_0 @ sk_B)
% 0.33/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.33/0.52          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.33/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.33/0.52  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('21', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('22', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.33/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.33/0.52          | (v1_xboole_0 @ sk_A)
% 0.33/0.52          | (v1_xboole_0 @ sk_B))),
% 0.33/0.52      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.33/0.52  thf('23', plain,
% 0.33/0.52      (((v1_xboole_0 @ sk_B)
% 0.33/0.52        | (v1_xboole_0 @ sk_A)
% 0.33/0.52        | (m1_subset_1 @ 
% 0.33/0.52           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.33/0.52      inference('sup-', [status(thm)], ['16', '22'])).
% 0.33/0.52  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('25', plain,
% 0.33/0.52      (((m1_subset_1 @ 
% 0.33/0.52         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.33/0.52        | (v1_xboole_0 @ sk_A))),
% 0.33/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.33/0.52  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('27', plain,
% 0.33/0.52      ((m1_subset_1 @ 
% 0.33/0.52        (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('clc', [status(thm)], ['25', '26'])).
% 0.33/0.52  thf('28', plain,
% 0.33/0.52      (![X8 : $i, X9 : $i]:
% 0.33/0.52         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.33/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.33/0.52      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.33/0.52  thf('29', plain,
% 0.33/0.52      (((k5_setfam_1 @ sk_A @ 
% 0.33/0.52         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.33/0.52         = (k3_tarski @ 
% 0.33/0.52            (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52             (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.33/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.33/0.52  thf('30', plain,
% 0.33/0.52      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.33/0.52          (k3_tarski @ 
% 0.33/0.52           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.33/0.52      inference('demod', [status(thm)], ['4', '29'])).
% 0.33/0.52  thf('31', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(dt_k5_setfam_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.33/0.52  thf('32', plain,
% 0.33/0.52      (![X6 : $i, X7 : $i]:
% 0.33/0.52         ((m1_subset_1 @ (k5_setfam_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.33/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.33/0.52      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.33/0.52  thf('33', plain,
% 0.33/0.52      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.33/0.52  thf('34', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 0.33/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.52  thf('35', plain, ((m1_subset_1 @ (k3_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.33/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.33/0.52  thf('36', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('37', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(t182_funct_2, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.33/0.52                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.33/0.52               ( ![D:$i]:
% 0.33/0.52                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.33/0.52                   ( ![E:$i]:
% 0.33/0.52                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.52                       ( ( m1_setfam_1 @ D @ E ) =>
% 0.33/0.52                         ( m1_setfam_1 @
% 0.33/0.52                           ( k6_funct_2 @
% 0.33/0.52                             A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ 
% 0.33/0.52                           E ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.52  thf('38', plain,
% 0.33/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.33/0.52         ((v1_xboole_0 @ X18)
% 0.33/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20)))
% 0.33/0.52          | ~ (m1_setfam_1 @ X19 @ X21)
% 0.33/0.52          | (m1_setfam_1 @ 
% 0.33/0.52             (k6_funct_2 @ X20 @ X18 @ X22 @ 
% 0.33/0.52              (k7_funct_2 @ X20 @ X18 @ X22 @ X19)) @ 
% 0.33/0.52             X21)
% 0.33/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20))
% 0.33/0.52          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.33/0.52          | ~ (v1_funct_2 @ X22 @ X20 @ X18)
% 0.33/0.52          | ~ (v1_funct_1 @ X22)
% 0.33/0.52          | (v1_xboole_0 @ X20))),
% 0.33/0.52      inference('cnf', [status(esa)], [t182_funct_2])).
% 0.33/0.52  thf('39', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.33/0.52         ((v1_xboole_0 @ sk_A)
% 0.33/0.52          | ~ (v1_funct_1 @ X0)
% 0.33/0.52          | ~ (v1_funct_2 @ X0 @ sk_A @ X1)
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.33/0.52          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_A))
% 0.33/0.52          | (m1_setfam_1 @ 
% 0.33/0.52             (k6_funct_2 @ sk_A @ X1 @ X0 @ 
% 0.33/0.52              (k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D)) @ 
% 0.33/0.52             X2)
% 0.33/0.52          | ~ (m1_setfam_1 @ sk_D @ X2)
% 0.33/0.52          | (v1_xboole_0 @ X1))),
% 0.33/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.33/0.52  thf('40', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v1_xboole_0 @ sk_B)
% 0.33/0.52          | ~ (m1_setfam_1 @ sk_D @ X0)
% 0.33/0.52          | (m1_setfam_1 @ 
% 0.33/0.52             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52              (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.33/0.52          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.33/0.52          | ~ (v1_funct_1 @ sk_C)
% 0.33/0.52          | (v1_xboole_0 @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.33/0.52  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('43', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((v1_xboole_0 @ sk_B)
% 0.33/0.52          | ~ (m1_setfam_1 @ sk_D @ X0)
% 0.33/0.52          | (m1_setfam_1 @ 
% 0.33/0.52             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52              (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52             X0)
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.33/0.52          | (v1_xboole_0 @ sk_A))),
% 0.33/0.52      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.33/0.52  thf('44', plain,
% 0.33/0.52      (((v1_xboole_0 @ sk_A)
% 0.33/0.52        | (m1_setfam_1 @ 
% 0.33/0.52           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52           (k3_tarski @ sk_D))
% 0.33/0.52        | ~ (m1_setfam_1 @ sk_D @ (k3_tarski @ sk_D))
% 0.33/0.52        | (v1_xboole_0 @ sk_B))),
% 0.33/0.52      inference('sup-', [status(thm)], ['35', '43'])).
% 0.33/0.52  thf(d10_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.33/0.52  thf('45', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.33/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.33/0.52  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.33/0.52      inference('simplify', [status(thm)], ['45'])).
% 0.33/0.52  thf(d12_setfam_1, axiom,
% 0.33/0.52    (![A:$i,B:$i]:
% 0.33/0.52     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.33/0.52  thf('47', plain,
% 0.33/0.52      (![X3 : $i, X5 : $i]:
% 0.33/0.52         ((m1_setfam_1 @ X5 @ X3) | ~ (r1_tarski @ X3 @ (k3_tarski @ X5)))),
% 0.33/0.52      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.33/0.52  thf('48', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.33/0.52  thf('49', plain,
% 0.33/0.52      (((v1_xboole_0 @ sk_A)
% 0.33/0.52        | (m1_setfam_1 @ 
% 0.33/0.52           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52           (k3_tarski @ sk_D))
% 0.33/0.52        | (v1_xboole_0 @ sk_B))),
% 0.33/0.52      inference('demod', [status(thm)], ['44', '48'])).
% 0.33/0.52  thf('50', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('51', plain,
% 0.33/0.52      (((v1_xboole_0 @ sk_B)
% 0.33/0.52        | (m1_setfam_1 @ 
% 0.33/0.52           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52           (k3_tarski @ sk_D)))),
% 0.33/0.52      inference('clc', [status(thm)], ['49', '50'])).
% 0.33/0.52  thf('52', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('53', plain,
% 0.33/0.52      ((m1_setfam_1 @ 
% 0.33/0.52        (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.33/0.52        (k3_tarski @ sk_D))),
% 0.33/0.52      inference('clc', [status(thm)], ['51', '52'])).
% 0.33/0.52  thf('54', plain,
% 0.33/0.52      (![X3 : $i, X4 : $i]:
% 0.33/0.52         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (m1_setfam_1 @ X4 @ X3))),
% 0.33/0.52      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.33/0.52  thf('55', plain,
% 0.33/0.52      ((r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.33/0.52        (k3_tarski @ 
% 0.33/0.52         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.33/0.52          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.33/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.33/0.52  thf('56', plain, ($false), inference('demod', [status(thm)], ['30', '55'])).
% 0.33/0.52  
% 0.33/0.52  % SZS output end Refutation
% 0.33/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

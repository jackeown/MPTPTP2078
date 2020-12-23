%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h6e2hGjAUj

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 214 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   18
%              Number of atoms          :  884 (4429 expanded)
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

thf(t183_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) )
                 => ( r1_tarski @ ( k5_setfam_1 @ B @ ( k7_funct_2 @ A @ B @ C @ ( k6_funct_2 @ A @ B @ C @ D ) ) ) @ ( k5_setfam_1 @ B @ D ) ) ) ) ) ) )).

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
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) )
                   => ( r1_tarski @ ( k5_setfam_1 @ B @ ( k7_funct_2 @ A @ B @ C @ ( k6_funct_2 @ A @ B @ C @ D ) ) ) @ ( k5_setfam_1 @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t183_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_setfam_1 @ sk_B @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) @ ( k5_setfam_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
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
    ( ( k5_setfam_1 @ sk_B @ sk_D )
    = ( k3_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k5_setfam_1 @ sk_B @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X11 @ X12 @ X10 @ X13 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
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
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
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
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k5_setfam_1 @ X9 @ X8 )
        = ( k3_tarski @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,
    ( ( k5_setfam_1 @ sk_B @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    = ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','29'])).

thf('31',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['25','26'])).

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
    m1_subset_1 @ ( k5_setfam_1 @ sk_B @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k5_setfam_1 @ sk_B @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    = ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('35',plain,(
    m1_subset_1 @ ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('38',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_setfam_1 @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t181_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                     => ( ( m1_setfam_1 @ ( k7_funct_2 @ A @ B @ C @ ( k6_funct_2 @ A @ B @ C @ D ) ) @ E )
                       => ( m1_setfam_1 @ D @ E ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ~ ( m1_setfam_1 @ ( k7_funct_2 @ X20 @ X18 @ X21 @ ( k6_funct_2 @ X20 @ X18 @ X21 @ X19 ) ) @ X22 )
      | ( m1_setfam_1 @ X19 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t181_funct_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( m1_setfam_1 @ sk_D @ X2 )
      | ~ ( m1_setfam_1 @ ( k7_funct_2 @ X0 @ sk_B @ X1 @ ( k6_funct_2 @ X0 @ sk_B @ X1 @ sk_D ) ) @ X2 )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( m1_setfam_1 @ sk_D @ ( k3_tarski @ ( k7_funct_2 @ X1 @ sk_B @ X0 @ ( k6_funct_2 @ X1 @ sk_B @ X0 @ sk_D ) ) ) )
      | ~ ( m1_subset_1 @ ( k3_tarski @ ( k7_funct_2 @ X1 @ sk_B @ X0 @ ( k6_funct_2 @ X1 @ sk_B @ X0 @ sk_D ) ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( m1_setfam_1 @ sk_D @ ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ sk_D @ ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ sk_D @ ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_setfam_1 @ sk_D @ ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( m1_setfam_1 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('54',plain,(
    r1_tarski @ ( k3_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) @ ( k3_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['30','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h6e2hGjAUj
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 53 iterations in 0.046s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.21/0.50  thf(t183_funct_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.50                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.21/0.50                   ( r1_tarski @
% 0.21/0.50                     ( k5_setfam_1 @
% 0.21/0.50                       B @ 
% 0.21/0.50                       ( k7_funct_2 @
% 0.21/0.50                         A @ B @ C @ ( k6_funct_2 @ A @ B @ C @ D ) ) ) @ 
% 0.21/0.50                     ( k5_setfam_1 @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.50                    ( m1_subset_1 @
% 0.21/0.50                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50                  ( ![D:$i]:
% 0.21/0.50                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.21/0.50                      ( r1_tarski @
% 0.21/0.50                        ( k5_setfam_1 @
% 0.21/0.50                          B @ 
% 0.21/0.50                          ( k7_funct_2 @
% 0.21/0.50                            A @ B @ C @ ( k6_funct_2 @ A @ B @ C @ D ) ) ) @ 
% 0.21/0.50                        ( k5_setfam_1 @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t183_funct_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (~ (r1_tarski @ 
% 0.21/0.50          (k5_setfam_1 @ sk_B @ 
% 0.21/0.50           (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.50            (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))) @ 
% 0.21/0.50          (k5_setfam_1 @ sk_B @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k5_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.50       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.21/0.51  thf('3', plain, (((k5_setfam_1 @ sk_B @ sk_D) = (k3_tarski @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (~ (r1_tarski @ 
% 0.21/0.51          (k5_setfam_1 @ sk_B @ 
% 0.21/0.51           (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51            (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))) @ 
% 0.21/0.51          (k3_tarski @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k6_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.21/0.51          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.21/0.51          | ~ (v1_funct_1 @ X10)
% 0.21/0.51          | (v1_xboole_0 @ X12)
% 0.21/0.51          | (v1_xboole_0 @ X11)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12)))
% 0.21/0.51          | (m1_subset_1 @ (k6_funct_2 @ X11 @ X12 @ X10 @ X13) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | (v1_xboole_0 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '11'])).
% 0.21/0.51  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.51      inference('clc', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_k7_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.21/0.51         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @
% 0.21/0.51         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.21/0.51          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.21/0.51          | ~ (v1_funct_1 @ X14)
% 0.21/0.51          | (v1_xboole_0 @ X16)
% 0.21/0.51          | (v1_xboole_0 @ X15)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.21/0.51          | (m1_subset_1 @ (k7_funct_2 @ X15 @ X16 @ X14 @ X17) @ 
% 0.21/0.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | (v1_xboole_0 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('21', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.21/0.51          | (v1_xboole_0 @ sk_A)
% 0.21/0.51          | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B)
% 0.21/0.51        | (v1_xboole_0 @ sk_A)
% 0.21/0.51        | (m1_subset_1 @ 
% 0.21/0.51           (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51            (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.21/0.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '22'])).
% 0.21/0.51  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((m1_subset_1 @ 
% 0.21/0.51         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51          (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.21/0.51         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('clc', [status(thm)], ['23', '24'])).
% 0.21/0.51  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((k5_setfam_1 @ sk_B @ 
% 0.21/0.51         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51          (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.51         = (k3_tarski @ 
% 0.21/0.51            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (~ (r1_tarski @ 
% 0.21/0.51          (k3_tarski @ 
% 0.21/0.51           (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51            (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))) @ 
% 0.21/0.51          (k3_tarski @ sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.51  thf(dt_k5_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k5_setfam_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6))
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (k5_setfam_1 @ sk_B @ 
% 0.21/0.51         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51          (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))) @ 
% 0.21/0.51        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (((k5_setfam_1 @ sk_B @ 
% 0.21/0.51         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51          (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.51         = (k3_tarski @ 
% 0.21/0.51            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((m1_subset_1 @ 
% 0.21/0.51        (k3_tarski @ 
% 0.21/0.51         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51          (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))) @ 
% 0.21/0.51        (k1_zfmisc_1 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(d10_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.51  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf(d12_setfam_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X3 : $i, X5 : $i]:
% 0.21/0.51         ((m1_setfam_1 @ X5 @ X3) | ~ (r1_tarski @ X3 @ (k3_tarski @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.51  thf('39', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t181_funct_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.51                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51               ( ![D:$i]:
% 0.21/0.51                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) =>
% 0.21/0.51                   ( ![E:$i]:
% 0.21/0.51                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.51                       ( ( m1_setfam_1 @
% 0.21/0.51                           ( k7_funct_2 @
% 0.21/0.51                             A @ B @ C @ ( k6_funct_2 @ A @ B @ C @ D ) ) @ 
% 0.21/0.51                           E ) =>
% 0.21/0.51                         ( m1_setfam_1 @ D @ E ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X18)
% 0.21/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 0.21/0.51          | ~ (m1_setfam_1 @ 
% 0.21/0.51               (k7_funct_2 @ X20 @ X18 @ X21 @ 
% 0.21/0.51                (k6_funct_2 @ X20 @ X18 @ X21 @ X19)) @ 
% 0.21/0.51               X22)
% 0.21/0.51          | (m1_setfam_1 @ X19 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X18))
% 0.21/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X18)))
% 0.21/0.51          | ~ (v1_funct_2 @ X21 @ X20 @ X18)
% 0.21/0.51          | ~ (v1_funct_1 @ X21)
% 0.21/0.51          | (v1_xboole_0 @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [t181_funct_2])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X0)
% 0.21/0.51          | ~ (v1_funct_1 @ X1)
% 0.21/0.51          | ~ (v1_funct_2 @ X1 @ X0 @ sk_B)
% 0.21/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.21/0.51          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_B))
% 0.21/0.51          | (m1_setfam_1 @ sk_D @ X2)
% 0.21/0.51          | ~ (m1_setfam_1 @ 
% 0.21/0.51               (k7_funct_2 @ X0 @ sk_B @ X1 @ 
% 0.21/0.51                (k6_funct_2 @ X0 @ sk_B @ X1 @ sk_D)) @ 
% 0.21/0.51               X2)
% 0.21/0.51          | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ sk_B)
% 0.21/0.51          | (m1_setfam_1 @ sk_D @ 
% 0.21/0.51             (k3_tarski @ 
% 0.21/0.51              (k7_funct_2 @ X1 @ sk_B @ X0 @ 
% 0.21/0.51               (k6_funct_2 @ X1 @ sk_B @ X0 @ sk_D))))
% 0.21/0.51          | ~ (m1_subset_1 @ 
% 0.21/0.51               (k3_tarski @ 
% 0.21/0.51                (k7_funct_2 @ X1 @ sk_B @ X0 @ 
% 0.21/0.51                 (k6_funct_2 @ X1 @ sk_B @ X0 @ sk_D))) @ 
% 0.21/0.51               (k1_zfmisc_1 @ sk_B))
% 0.21/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.21/0.51          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.21/0.51          | ~ (v1_funct_1 @ X0)
% 0.21/0.51          | (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['39', '42'])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.51        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.51        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.21/0.51        | (m1_setfam_1 @ sk_D @ 
% 0.21/0.51           (k3_tarski @ 
% 0.21/0.51            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['35', '43'])).
% 0.21/0.51  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('46', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | (m1_setfam_1 @ sk_D @ 
% 0.21/0.51           (k3_tarski @ 
% 0.21/0.51            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))
% 0.21/0.51        | (v1_xboole_0 @ sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.21/0.51  thf('49', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_B)
% 0.21/0.51        | (m1_setfam_1 @ sk_D @ 
% 0.21/0.51           (k3_tarski @ 
% 0.21/0.51            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))))),
% 0.21/0.51      inference('clc', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      ((m1_setfam_1 @ sk_D @ 
% 0.21/0.51        (k3_tarski @ 
% 0.21/0.51         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51          (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.21/0.51      inference('clc', [status(thm)], ['50', '51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (m1_setfam_1 @ X4 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      ((r1_tarski @ 
% 0.21/0.51        (k3_tarski @ 
% 0.21/0.51         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.51          (k6_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))) @ 
% 0.21/0.51        (k3_tarski @ sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.51  thf('55', plain, ($false), inference('demod', [status(thm)], ['30', '54'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

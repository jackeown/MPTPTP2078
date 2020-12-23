%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5orhUE2KlO

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:56 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 128 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  859 (2252 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_funct_2_type,type,(
    k6_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X9: $i,X10: $i] :
      ( ( ( k5_setfam_1 @ X10 @ X9 )
        = ( k3_tarski @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X19 @ X20 @ X18 @ X21 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X16 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X15 @ X16 @ X14 @ X17 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( ( k5_setfam_1 @ X10 @ X9 )
        = ( k3_tarski @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
    = ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ ( k3_tarski @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('34',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('35',plain,(
    ! [X5: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X5 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('36',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) )
      | ~ ( m1_setfam_1 @ X23 @ X25 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ X24 @ X22 @ X26 @ ( k7_funct_2 @ X24 @ X22 @ X26 @ X23 ) ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X22 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t182_funct_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ X1 @ X0 @ ( k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D ) ) @ X2 )
      | ~ ( m1_setfam_1 @ sk_D @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ~ ( m1_setfam_1 @ sk_D @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('50',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_setfam_1 @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['47','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) @ ( k3_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( m1_setfam_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('58',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['4','29','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5orhUE2KlO
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.61  % Solved by: fo/fo7.sh
% 0.37/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.61  % done 333 iterations in 0.155s
% 0.37/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.61  % SZS output start Refutation
% 0.37/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.61  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 0.37/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.61  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 0.37/0.61  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.37/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.61  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.37/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.37/0.61  thf(t184_funct_2, conjecture,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61               ( ![D:$i]:
% 0.37/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61                   ( r1_tarski @
% 0.37/0.61                     ( k5_setfam_1 @ A @ D ) @ 
% 0.37/0.61                     ( k5_setfam_1 @
% 0.37/0.61                       A @ 
% 0.37/0.61                       ( k6_funct_2 @
% 0.37/0.61                         A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.61    (~( ![A:$i]:
% 0.37/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61          ( ![B:$i]:
% 0.37/0.61            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61              ( ![C:$i]:
% 0.37/0.61                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61                    ( m1_subset_1 @
% 0.37/0.61                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61                  ( ![D:$i]:
% 0.37/0.61                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61                      ( r1_tarski @
% 0.37/0.61                        ( k5_setfam_1 @ A @ D ) @ 
% 0.37/0.61                        ( k5_setfam_1 @
% 0.37/0.61                          A @ 
% 0.37/0.61                          ( k6_funct_2 @
% 0.37/0.61                            A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.61    inference('cnf.neg', [status(esa)], [t184_funct_2])).
% 0.37/0.61  thf('0', plain,
% 0.37/0.61      (~ (r1_tarski @ (k5_setfam_1 @ sk_A @ sk_D) @ 
% 0.37/0.61          (k5_setfam_1 @ sk_A @ 
% 0.37/0.61           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('1', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(redefinition_k5_setfam_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.37/0.61  thf('2', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         (((k5_setfam_1 @ X10 @ X9) = (k3_tarski @ X9))
% 0.37/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.37/0.61  thf('3', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 0.37/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.61  thf('4', plain,
% 0.37/0.61      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.37/0.61          (k5_setfam_1 @ sk_A @ 
% 0.37/0.61           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.37/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.61  thf('5', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('6', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(dt_k7_funct_2, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 0.37/0.61       ( m1_subset_1 @
% 0.37/0.61         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 0.37/0.61  thf('7', plain,
% 0.37/0.61      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.37/0.61          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.37/0.61          | ~ (v1_funct_1 @ X18)
% 0.37/0.61          | (v1_xboole_0 @ X20)
% 0.37/0.61          | (v1_xboole_0 @ X19)
% 0.37/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19)))
% 0.37/0.61          | (m1_subset_1 @ (k7_funct_2 @ X19 @ X20 @ X18 @ X21) @ 
% 0.37/0.61             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 0.37/0.61  thf('8', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.37/0.61          | (v1_xboole_0 @ sk_A)
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.61  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('11', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.37/0.61          | (v1_xboole_0 @ sk_A)
% 0.37/0.61          | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.37/0.61  thf('12', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['5', '11'])).
% 0.37/0.61  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('14', plain,
% 0.37/0.61      (((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.61         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['12', '13'])).
% 0.37/0.61  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('16', plain,
% 0.37/0.61      ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.37/0.61        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 0.37/0.61      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.61  thf('17', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(dt_k6_funct_2, axiom,
% 0.37/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.37/0.61         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.37/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 0.37/0.61       ( m1_subset_1 @
% 0.37/0.61         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.37/0.61  thf('18', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.61         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.37/0.61          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 0.37/0.61          | ~ (v1_funct_1 @ X14)
% 0.37/0.61          | (v1_xboole_0 @ X16)
% 0.37/0.61          | (v1_xboole_0 @ X15)
% 0.37/0.61          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X16)))
% 0.37/0.61          | (m1_subset_1 @ (k6_funct_2 @ X15 @ X16 @ X14 @ X17) @ 
% 0.37/0.61             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.37/0.61      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 0.37/0.61  thf('19', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.37/0.61          | (v1_xboole_0 @ sk_A)
% 0.37/0.61          | (v1_xboole_0 @ sk_B)
% 0.37/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.37/0.61          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.61  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('21', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('22', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C @ X0) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 0.37/0.61          | (v1_xboole_0 @ sk_A)
% 0.37/0.61          | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.37/0.61  thf('23', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B)
% 0.37/0.61        | (v1_xboole_0 @ sk_A)
% 0.37/0.61        | (m1_subset_1 @ 
% 0.37/0.61           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['16', '22'])).
% 0.37/0.61  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('25', plain,
% 0.37/0.61      (((m1_subset_1 @ 
% 0.37/0.61         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.37/0.61        | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('clc', [status(thm)], ['23', '24'])).
% 0.37/0.61  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('27', plain,
% 0.37/0.61      ((m1_subset_1 @ 
% 0.37/0.61        (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.61      inference('clc', [status(thm)], ['25', '26'])).
% 0.37/0.61  thf('28', plain,
% 0.37/0.61      (![X9 : $i, X10 : $i]:
% 0.37/0.61         (((k5_setfam_1 @ X10 @ X9) = (k3_tarski @ X9))
% 0.37/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.37/0.61      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.37/0.61  thf('29', plain,
% 0.37/0.61      (((k5_setfam_1 @ sk_A @ 
% 0.37/0.61         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.37/0.61         = (k3_tarski @ 
% 0.37/0.61            (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61             (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.61  thf('30', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t3_subset, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.61  thf('31', plain,
% 0.37/0.61      (![X11 : $i, X12 : $i]:
% 0.37/0.61         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('32', plain, ((r1_tarski @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.61  thf(t95_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( r1_tarski @ A @ B ) =>
% 0.37/0.61       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.37/0.61  thf('33', plain,
% 0.37/0.61      (![X3 : $i, X4 : $i]:
% 0.37/0.61         ((r1_tarski @ (k3_tarski @ X3) @ (k3_tarski @ X4))
% 0.37/0.61          | ~ (r1_tarski @ X3 @ X4))),
% 0.37/0.61      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.37/0.61  thf('34', plain,
% 0.37/0.61      ((r1_tarski @ (k3_tarski @ sk_D) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf(t99_zfmisc_1, axiom,
% 0.37/0.61    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.37/0.61  thf('35', plain, (![X5 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X5)) = (X5))),
% 0.37/0.61      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.37/0.61  thf('36', plain, ((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)),
% 0.37/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.61  thf('37', plain,
% 0.37/0.61      (![X11 : $i, X13 : $i]:
% 0.37/0.61         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.37/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.61  thf('38', plain, ((m1_subset_1 @ (k3_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.61  thf('39', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('40', plain,
% 0.37/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf(t182_funct_2, axiom,
% 0.37/0.61    (![A:$i]:
% 0.37/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.61       ( ![B:$i]:
% 0.37/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.37/0.61           ( ![C:$i]:
% 0.37/0.61             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.61               ( ![D:$i]:
% 0.37/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.37/0.61                   ( ![E:$i]:
% 0.37/0.61                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.61                       ( ( m1_setfam_1 @ D @ E ) =>
% 0.37/0.61                         ( m1_setfam_1 @
% 0.37/0.61                           ( k6_funct_2 @
% 0.37/0.61                             A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ 
% 0.37/0.61                           E ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.61  thf('41', plain,
% 0.37/0.61      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ X22)
% 0.37/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24)))
% 0.37/0.61          | ~ (m1_setfam_1 @ X23 @ X25)
% 0.37/0.61          | (m1_setfam_1 @ 
% 0.37/0.61             (k6_funct_2 @ X24 @ X22 @ X26 @ 
% 0.37/0.61              (k7_funct_2 @ X24 @ X22 @ X26 @ X23)) @ 
% 0.37/0.61             X25)
% 0.37/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24))
% 0.37/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 0.37/0.61          | ~ (v1_funct_2 @ X26 @ X24 @ X22)
% 0.37/0.61          | ~ (v1_funct_1 @ X26)
% 0.37/0.61          | (v1_xboole_0 @ X24))),
% 0.37/0.61      inference('cnf', [status(esa)], [t182_funct_2])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ sk_A)
% 0.37/0.61          | ~ (v1_funct_1 @ X0)
% 0.37/0.61          | ~ (v1_funct_2 @ X0 @ sk_A @ X1)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.37/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61          | (m1_setfam_1 @ 
% 0.37/0.61             (k6_funct_2 @ sk_A @ X1 @ X0 @ 
% 0.37/0.61              (k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D)) @ 
% 0.37/0.61             X2)
% 0.37/0.61          | ~ (m1_setfam_1 @ sk_D @ X2)
% 0.37/0.61          | (v1_xboole_0 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ sk_B)
% 0.37/0.61          | ~ (m1_setfam_1 @ sk_D @ X0)
% 0.37/0.61          | (m1_setfam_1 @ 
% 0.37/0.61             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61              (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61             X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.37/0.61          | ~ (v1_funct_1 @ sk_C)
% 0.37/0.61          | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('sup-', [status(thm)], ['39', '42'])).
% 0.37/0.61  thf('44', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (![X0 : $i]:
% 0.37/0.61         ((v1_xboole_0 @ sk_B)
% 0.37/0.61          | ~ (m1_setfam_1 @ sk_D @ X0)
% 0.37/0.61          | (m1_setfam_1 @ 
% 0.37/0.61             (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61              (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61             X0)
% 0.37/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.37/0.61          | (v1_xboole_0 @ sk_A))),
% 0.37/0.61      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_A)
% 0.37/0.61        | (m1_setfam_1 @ 
% 0.37/0.61           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61           (k3_tarski @ sk_D))
% 0.37/0.61        | ~ (m1_setfam_1 @ sk_D @ (k3_tarski @ sk_D))
% 0.37/0.61        | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['38', '46'])).
% 0.37/0.61  thf(d10_xboole_0, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.61  thf('48', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.61  thf('49', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.61      inference('simplify', [status(thm)], ['48'])).
% 0.37/0.61  thf(d12_setfam_1, axiom,
% 0.37/0.61    (![A:$i,B:$i]:
% 0.37/0.61     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.37/0.61  thf('50', plain,
% 0.37/0.61      (![X6 : $i, X8 : $i]:
% 0.37/0.61         ((m1_setfam_1 @ X8 @ X6) | ~ (r1_tarski @ X6 @ (k3_tarski @ X8)))),
% 0.37/0.61      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.37/0.61  thf('51', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_A)
% 0.37/0.61        | (m1_setfam_1 @ 
% 0.37/0.61           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61           (k3_tarski @ sk_D))
% 0.37/0.61        | (v1_xboole_0 @ sk_B))),
% 0.37/0.61      inference('demod', [status(thm)], ['47', '51'])).
% 0.37/0.61  thf('53', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('54', plain,
% 0.37/0.61      (((v1_xboole_0 @ sk_B)
% 0.37/0.61        | (m1_setfam_1 @ 
% 0.37/0.61           (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61            (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61           (k3_tarski @ sk_D)))),
% 0.37/0.61      inference('clc', [status(thm)], ['52', '53'])).
% 0.37/0.61  thf('55', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('56', plain,
% 0.37/0.61      ((m1_setfam_1 @ 
% 0.37/0.61        (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61         (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)) @ 
% 0.37/0.61        (k3_tarski @ sk_D))),
% 0.37/0.61      inference('clc', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain,
% 0.37/0.61      (![X6 : $i, X7 : $i]:
% 0.37/0.61         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (m1_setfam_1 @ X7 @ X6))),
% 0.37/0.61      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.37/0.61  thf('58', plain,
% 0.37/0.61      ((r1_tarski @ (k3_tarski @ sk_D) @ 
% 0.37/0.61        (k3_tarski @ 
% 0.37/0.61         (k6_funct_2 @ sk_A @ sk_B @ sk_C @ 
% 0.37/0.61          (k7_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))))),
% 0.37/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.61  thf('59', plain, ($false),
% 0.37/0.61      inference('demod', [status(thm)], ['4', '29', '58'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

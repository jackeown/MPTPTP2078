%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OazMu8lDqV

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:55 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 136 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  938 (2334 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k6_funct_2_type,type,(
    k6_funct_2: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( r1_tarski @ ( k5_setfam_1 @ sk_A @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ( ( k5_setfam_1 @ X17 @ X16 )
        = ( k3_tarski @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_D )
    = ( k3_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X26 @ X27 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X22 @ X23 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k5_setfam_1 @ X17 @ X16 )
        = ( k3_tarski @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) )
    = ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['4','29'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('40',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A )
    | ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X31 ) ) )
      | ~ ( m1_setfam_1 @ X30 @ X32 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ X31 @ X29 @ X33 @ ( k7_funct_2 @ X31 @ X29 @ X33 @ X30 ) ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t182_funct_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ X1 @ X0 @ ( k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D ) ) @ X2 )
      | ~ ( m1_setfam_1 @ sk_D @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ~ ( m1_setfam_1 @ sk_D @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['53'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_setfam_1 @ X15 @ X13 )
      | ~ ( r1_tarski @ X13 @ ( k3_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['52','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ ( k3_tarski @ X14 ) )
      | ~ ( m1_setfam_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('63',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['30','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OazMu8lDqV
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:08:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.15/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.15/1.35  % Solved by: fo/fo7.sh
% 1.15/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.35  % done 824 iterations in 0.902s
% 1.15/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.15/1.35  % SZS output start Refutation
% 1.15/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.35  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 1.15/1.35  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.15/1.35  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 1.15/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.35  thf(sk_D_type, type, sk_D: $i).
% 1.15/1.35  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.15/1.35  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.15/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.35  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 1.15/1.35  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.15/1.35  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.15/1.35  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.15/1.35  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.15/1.35  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.15/1.35  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.35  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.35  thf(t184_funct_2, conjecture,
% 1.15/1.35    (![A:$i]:
% 1.15/1.35     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.15/1.35       ( ![B:$i]:
% 1.15/1.35         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.15/1.35           ( ![C:$i]:
% 1.15/1.35             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.35                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.35               ( ![D:$i]:
% 1.15/1.35                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.15/1.35                   ( r1_tarski @
% 1.15/1.35                     ( k5_setfam_1 @ A @ D ) @ 
% 1.15/1.35                     ( k5_setfam_1 @
% 1.15/1.35                       A @ 
% 1.15/1.35                       ( k6_funct_2 @
% 1.15/1.35                         A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 1.15/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.35    (~( ![A:$i]:
% 1.15/1.35        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.15/1.35          ( ![B:$i]:
% 1.15/1.35            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.15/1.35              ( ![C:$i]:
% 1.15/1.35                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.35                    ( m1_subset_1 @
% 1.15/1.35                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.35                  ( ![D:$i]:
% 1.15/1.35                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.15/1.35                      ( r1_tarski @
% 1.15/1.35                        ( k5_setfam_1 @ A @ D ) @ 
% 1.15/1.35                        ( k5_setfam_1 @
% 1.15/1.35                          A @ 
% 1.15/1.35                          ( k6_funct_2 @
% 1.15/1.35                            A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 1.15/1.35    inference('cnf.neg', [status(esa)], [t184_funct_2])).
% 1.15/1.35  thf('0', plain,
% 1.15/1.35      (~ (r1_tarski @ (k5_setfam_1 @ sk_A @ sk_D) @ 
% 1.15/1.35          (k5_setfam_1 @ sk_A @ 
% 1.15/1.35           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('1', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(redefinition_k5_setfam_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.15/1.35       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 1.15/1.35  thf('2', plain,
% 1.15/1.35      (![X16 : $i, X17 : $i]:
% 1.15/1.35         (((k5_setfam_1 @ X17 @ X16) = (k3_tarski @ X16))
% 1.15/1.35          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.15/1.35  thf('3', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 1.15/1.35      inference('sup-', [status(thm)], ['1', '2'])).
% 1.15/1.35  thf('4', plain,
% 1.15/1.35      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 1.15/1.35          (k5_setfam_1 @ sk_A @ 
% 1.15/1.35           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 1.15/1.35      inference('demod', [status(thm)], ['0', '3'])).
% 1.15/1.35  thf('5', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('6', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(dt_k7_funct_2, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.15/1.35         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 1.15/1.35       ( m1_subset_1 @
% 1.15/1.35         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 1.15/1.35  thf('7', plain,
% 1.15/1.35      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.35         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.15/1.35          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 1.15/1.35          | ~ (v1_funct_1 @ X25)
% 1.15/1.35          | (v1_xboole_0 @ X27)
% 1.15/1.35          | (v1_xboole_0 @ X26)
% 1.15/1.35          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X26)))
% 1.15/1.35          | (m1_subset_1 @ (k7_funct_2 @ X26 @ X27 @ X25 @ X28) @ 
% 1.15/1.35             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 1.15/1.35      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 1.15/1.35  thf('8', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.15/1.35          | (v1_xboole_0 @ sk_A)
% 1.15/1.35          | (v1_xboole_0 @ sk_B)
% 1.15/1.35          | ~ (v1_funct_1 @ sk_C_2)
% 1.15/1.35          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 1.15/1.35      inference('sup-', [status(thm)], ['6', '7'])).
% 1.15/1.35  thf('9', plain, ((v1_funct_1 @ sk_C_2)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('10', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('11', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.15/1.35          | (v1_xboole_0 @ sk_A)
% 1.15/1.35          | (v1_xboole_0 @ sk_B))),
% 1.15/1.35      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.15/1.35  thf('12', plain,
% 1.15/1.35      (((v1_xboole_0 @ sk_B)
% 1.15/1.35        | (v1_xboole_0 @ sk_A)
% 1.15/1.35        | (m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['5', '11'])).
% 1.15/1.35  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('14', plain,
% 1.15/1.35      (((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D) @ 
% 1.15/1.35         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.15/1.35        | (v1_xboole_0 @ sk_A))),
% 1.15/1.35      inference('clc', [status(thm)], ['12', '13'])).
% 1.15/1.35  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('16', plain,
% 1.15/1.35      ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D) @ 
% 1.15/1.35        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 1.15/1.35      inference('clc', [status(thm)], ['14', '15'])).
% 1.15/1.35  thf('17', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(dt_k6_funct_2, axiom,
% 1.15/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.15/1.35     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.15/1.35         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.35         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.15/1.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 1.15/1.35       ( m1_subset_1 @
% 1.15/1.35         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.15/1.35  thf('18', plain,
% 1.15/1.35      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.15/1.35         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 1.15/1.35          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 1.15/1.35          | ~ (v1_funct_1 @ X21)
% 1.15/1.35          | (v1_xboole_0 @ X23)
% 1.15/1.35          | (v1_xboole_0 @ X22)
% 1.15/1.35          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23)))
% 1.15/1.35          | (m1_subset_1 @ (k6_funct_2 @ X22 @ X23 @ X21 @ X24) @ 
% 1.15/1.35             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 1.15/1.35      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 1.15/1.35  thf('19', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.15/1.35          | (v1_xboole_0 @ sk_A)
% 1.15/1.35          | (v1_xboole_0 @ sk_B)
% 1.15/1.35          | ~ (v1_funct_1 @ sk_C_2)
% 1.15/1.35          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 1.15/1.35      inference('sup-', [status(thm)], ['17', '18'])).
% 1.15/1.35  thf('20', plain, ((v1_funct_1 @ sk_C_2)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('21', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('22', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.15/1.35          | (v1_xboole_0 @ sk_A)
% 1.15/1.35          | (v1_xboole_0 @ sk_B))),
% 1.15/1.35      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.15/1.35  thf('23', plain,
% 1.15/1.35      (((v1_xboole_0 @ sk_B)
% 1.15/1.35        | (v1_xboole_0 @ sk_A)
% 1.15/1.35        | (m1_subset_1 @ 
% 1.15/1.35           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['16', '22'])).
% 1.15/1.35  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('25', plain,
% 1.15/1.35      (((m1_subset_1 @ 
% 1.15/1.35         (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35          (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.15/1.35        | (v1_xboole_0 @ sk_A))),
% 1.15/1.35      inference('clc', [status(thm)], ['23', '24'])).
% 1.15/1.35  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('27', plain,
% 1.15/1.35      ((m1_subset_1 @ 
% 1.15/1.35        (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35         (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.35      inference('clc', [status(thm)], ['25', '26'])).
% 1.15/1.35  thf('28', plain,
% 1.15/1.35      (![X16 : $i, X17 : $i]:
% 1.15/1.35         (((k5_setfam_1 @ X17 @ X16) = (k3_tarski @ X16))
% 1.15/1.35          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 1.15/1.35      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.15/1.35  thf('29', plain,
% 1.15/1.35      (((k5_setfam_1 @ sk_A @ 
% 1.15/1.35         (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35          (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)))
% 1.15/1.35         = (k3_tarski @ 
% 1.15/1.35            (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35             (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['27', '28'])).
% 1.15/1.35  thf('30', plain,
% 1.15/1.35      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 1.15/1.35          (k3_tarski @ 
% 1.15/1.35           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 1.15/1.35      inference('demod', [status(thm)], ['4', '29'])).
% 1.15/1.35  thf(t94_zfmisc_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 1.15/1.35       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 1.15/1.35  thf('31', plain,
% 1.15/1.35      (![X8 : $i, X9 : $i]:
% 1.15/1.35         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 1.15/1.35          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 1.15/1.35      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 1.15/1.35  thf('32', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(l3_subset_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.35       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.15/1.35  thf('33', plain,
% 1.15/1.35      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X10 @ X11)
% 1.15/1.35          | (r2_hidden @ X10 @ X12)
% 1.15/1.35          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 1.15/1.35      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.15/1.35  thf('34', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_D))),
% 1.15/1.35      inference('sup-', [status(thm)], ['32', '33'])).
% 1.15/1.35  thf('35', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 1.15/1.35          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D) @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.35      inference('sup-', [status(thm)], ['31', '34'])).
% 1.15/1.35  thf(d1_zfmisc_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.15/1.35       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.15/1.35  thf('36', plain,
% 1.15/1.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.15/1.35         (~ (r2_hidden @ X6 @ X5)
% 1.15/1.35          | (r1_tarski @ X6 @ X4)
% 1.15/1.35          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.15/1.35  thf('37', plain,
% 1.15/1.35      (![X4 : $i, X6 : $i]:
% 1.15/1.35         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 1.15/1.35      inference('simplify', [status(thm)], ['36'])).
% 1.15/1.35  thf('38', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 1.15/1.35          | (r1_tarski @ (sk_C_1 @ X0 @ sk_D) @ sk_A))),
% 1.15/1.35      inference('sup-', [status(thm)], ['35', '37'])).
% 1.15/1.35  thf('39', plain,
% 1.15/1.35      (![X8 : $i, X9 : $i]:
% 1.15/1.35         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 1.15/1.35          | ~ (r1_tarski @ (sk_C_1 @ X9 @ X8) @ X9))),
% 1.15/1.35      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 1.15/1.35  thf('40', plain,
% 1.15/1.35      (((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)
% 1.15/1.35        | (r1_tarski @ (k3_tarski @ sk_D) @ sk_A))),
% 1.15/1.35      inference('sup-', [status(thm)], ['38', '39'])).
% 1.15/1.35  thf('41', plain, ((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)),
% 1.15/1.35      inference('simplify', [status(thm)], ['40'])).
% 1.15/1.35  thf(t3_subset, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.15/1.35  thf('42', plain,
% 1.15/1.35      (![X18 : $i, X20 : $i]:
% 1.15/1.35         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 1.15/1.35      inference('cnf', [status(esa)], [t3_subset])).
% 1.15/1.35  thf('43', plain, ((m1_subset_1 @ (k3_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 1.15/1.35      inference('sup-', [status(thm)], ['41', '42'])).
% 1.15/1.35  thf('44', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('45', plain,
% 1.15/1.35      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf(t182_funct_2, axiom,
% 1.15/1.35    (![A:$i]:
% 1.15/1.35     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.15/1.35       ( ![B:$i]:
% 1.15/1.35         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.15/1.35           ( ![C:$i]:
% 1.15/1.35             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.15/1.35                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.15/1.35               ( ![D:$i]:
% 1.15/1.35                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.15/1.35                   ( ![E:$i]:
% 1.15/1.35                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.35                       ( ( m1_setfam_1 @ D @ E ) =>
% 1.15/1.35                         ( m1_setfam_1 @
% 1.15/1.35                           ( k6_funct_2 @
% 1.15/1.35                             A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ 
% 1.15/1.35                           E ) ) ) ) ) ) ) ) ) ) ))).
% 1.15/1.35  thf('46', plain,
% 1.15/1.35      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.15/1.35         ((v1_xboole_0 @ X29)
% 1.15/1.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X31)))
% 1.15/1.35          | ~ (m1_setfam_1 @ X30 @ X32)
% 1.15/1.35          | (m1_setfam_1 @ 
% 1.15/1.35             (k6_funct_2 @ X31 @ X29 @ X33 @ 
% 1.15/1.35              (k7_funct_2 @ X31 @ X29 @ X33 @ X30)) @ 
% 1.15/1.35             X32)
% 1.15/1.35          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 1.15/1.35          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 1.15/1.35          | ~ (v1_funct_2 @ X33 @ X31 @ X29)
% 1.15/1.35          | ~ (v1_funct_1 @ X33)
% 1.15/1.35          | (v1_xboole_0 @ X31))),
% 1.15/1.35      inference('cnf', [status(esa)], [t182_funct_2])).
% 1.15/1.35  thf('47', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.35         ((v1_xboole_0 @ sk_A)
% 1.15/1.35          | ~ (v1_funct_1 @ X0)
% 1.15/1.35          | ~ (v1_funct_2 @ X0 @ sk_A @ X1)
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 1.15/1.35          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_A))
% 1.15/1.35          | (m1_setfam_1 @ 
% 1.15/1.35             (k6_funct_2 @ sk_A @ X1 @ X0 @ 
% 1.15/1.35              (k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D)) @ 
% 1.15/1.35             X2)
% 1.15/1.35          | ~ (m1_setfam_1 @ sk_D @ X2)
% 1.15/1.35          | (v1_xboole_0 @ X1))),
% 1.15/1.35      inference('sup-', [status(thm)], ['45', '46'])).
% 1.15/1.35  thf('48', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((v1_xboole_0 @ sk_B)
% 1.15/1.35          | ~ (m1_setfam_1 @ sk_D @ X0)
% 1.15/1.35          | (m1_setfam_1 @ 
% 1.15/1.35             (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35              (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35             X0)
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.15/1.35          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 1.15/1.35          | ~ (v1_funct_1 @ sk_C_2)
% 1.15/1.35          | (v1_xboole_0 @ sk_A))),
% 1.15/1.35      inference('sup-', [status(thm)], ['44', '47'])).
% 1.15/1.35  thf('49', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('50', plain, ((v1_funct_1 @ sk_C_2)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('51', plain,
% 1.15/1.35      (![X0 : $i]:
% 1.15/1.35         ((v1_xboole_0 @ sk_B)
% 1.15/1.35          | ~ (m1_setfam_1 @ sk_D @ X0)
% 1.15/1.35          | (m1_setfam_1 @ 
% 1.15/1.35             (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35              (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35             X0)
% 1.15/1.35          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.15/1.35          | (v1_xboole_0 @ sk_A))),
% 1.15/1.35      inference('demod', [status(thm)], ['48', '49', '50'])).
% 1.15/1.35  thf('52', plain,
% 1.15/1.35      (((v1_xboole_0 @ sk_A)
% 1.15/1.35        | (m1_setfam_1 @ 
% 1.15/1.35           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35           (k3_tarski @ sk_D))
% 1.15/1.35        | ~ (m1_setfam_1 @ sk_D @ (k3_tarski @ sk_D))
% 1.15/1.35        | (v1_xboole_0 @ sk_B))),
% 1.15/1.35      inference('sup-', [status(thm)], ['43', '51'])).
% 1.15/1.35  thf(d10_xboole_0, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.15/1.35  thf('53', plain,
% 1.15/1.35      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.15/1.35  thf('54', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.15/1.35      inference('simplify', [status(thm)], ['53'])).
% 1.15/1.35  thf(d12_setfam_1, axiom,
% 1.15/1.35    (![A:$i,B:$i]:
% 1.15/1.35     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 1.15/1.35  thf('55', plain,
% 1.15/1.35      (![X13 : $i, X15 : $i]:
% 1.15/1.35         ((m1_setfam_1 @ X15 @ X13) | ~ (r1_tarski @ X13 @ (k3_tarski @ X15)))),
% 1.15/1.35      inference('cnf', [status(esa)], [d12_setfam_1])).
% 1.15/1.35  thf('56', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 1.15/1.35      inference('sup-', [status(thm)], ['54', '55'])).
% 1.15/1.35  thf('57', plain,
% 1.15/1.35      (((v1_xboole_0 @ sk_A)
% 1.15/1.35        | (m1_setfam_1 @ 
% 1.15/1.35           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35           (k3_tarski @ sk_D))
% 1.15/1.35        | (v1_xboole_0 @ sk_B))),
% 1.15/1.35      inference('demod', [status(thm)], ['52', '56'])).
% 1.15/1.35  thf('58', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('59', plain,
% 1.15/1.35      (((v1_xboole_0 @ sk_B)
% 1.15/1.35        | (m1_setfam_1 @ 
% 1.15/1.35           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35           (k3_tarski @ sk_D)))),
% 1.15/1.35      inference('clc', [status(thm)], ['57', '58'])).
% 1.15/1.35  thf('60', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.15/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.35  thf('61', plain,
% 1.15/1.35      ((m1_setfam_1 @ 
% 1.15/1.35        (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35         (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 1.15/1.35        (k3_tarski @ sk_D))),
% 1.15/1.35      inference('clc', [status(thm)], ['59', '60'])).
% 1.15/1.35  thf('62', plain,
% 1.15/1.35      (![X13 : $i, X14 : $i]:
% 1.15/1.35         ((r1_tarski @ X13 @ (k3_tarski @ X14)) | ~ (m1_setfam_1 @ X14 @ X13))),
% 1.15/1.35      inference('cnf', [status(esa)], [d12_setfam_1])).
% 1.15/1.35  thf('63', plain,
% 1.15/1.35      ((r1_tarski @ (k3_tarski @ sk_D) @ 
% 1.15/1.35        (k3_tarski @ 
% 1.15/1.35         (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 1.15/1.35          (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 1.15/1.35      inference('sup-', [status(thm)], ['61', '62'])).
% 1.15/1.35  thf('64', plain, ($false), inference('demod', [status(thm)], ['30', '63'])).
% 1.15/1.35  
% 1.15/1.35  % SZS output end Refutation
% 1.15/1.35  
% 1.15/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

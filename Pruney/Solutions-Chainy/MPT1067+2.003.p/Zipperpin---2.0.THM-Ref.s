%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9TQ7Nqbgnp

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:56 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 135 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  918 (2321 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k6_funct_2_type,type,(
    k6_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k5_setfam_1 @ sk_A @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) ) ) ),
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
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X21 @ X22 @ X20 @ X23 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 )
      | ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X17 @ X18 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k5_setfam_1 @ X9 @ X8 )
        = ( k3_tarski @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) )
    = ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['4','29'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X3 ) @ X4 )
      | ~ ( r1_tarski @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A )
    | ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) )
      | ~ ( m1_setfam_1 @ X25 @ X27 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ X26 @ X24 @ X28 @ ( k7_funct_2 @ X26 @ X24 @ X28 @ X25 ) ) @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X24 )
      | ~ ( v1_funct_1 @ X28 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t182_funct_2])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ X1 @ X0 @ ( k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D ) ) @ X2 )
      | ~ ( m1_setfam_1 @ sk_D @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ~ ( m1_setfam_1 @ sk_D @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('54',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_setfam_1 @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ ( k3_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ ( k3_tarski @ X6 ) )
      | ~ ( m1_setfam_1 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('62',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['30','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9TQ7Nqbgnp
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:17:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.34/2.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.34/2.58  % Solved by: fo/fo7.sh
% 2.34/2.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.34/2.58  % done 1104 iterations in 2.113s
% 2.34/2.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.34/2.58  % SZS output start Refutation
% 2.34/2.58  thf(sk_A_type, type, sk_A: $i).
% 2.34/2.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.34/2.58  thf(sk_B_type, type, sk_B: $i).
% 2.34/2.58  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 2.34/2.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.34/2.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.34/2.58  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.34/2.58  thf(sk_D_type, type, sk_D: $i).
% 2.34/2.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.34/2.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.34/2.58  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 2.34/2.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.34/2.58  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 2.34/2.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.34/2.58  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 2.34/2.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.34/2.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.34/2.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.34/2.58  thf(t184_funct_2, conjecture,
% 2.34/2.58    (![A:$i]:
% 2.34/2.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.34/2.58       ( ![B:$i]:
% 2.34/2.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.34/2.58           ( ![C:$i]:
% 2.34/2.58             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.58                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.58               ( ![D:$i]:
% 2.34/2.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.34/2.58                   ( r1_tarski @
% 2.34/2.58                     ( k5_setfam_1 @ A @ D ) @ 
% 2.34/2.58                     ( k5_setfam_1 @
% 2.34/2.58                       A @ 
% 2.34/2.58                       ( k6_funct_2 @
% 2.34/2.58                         A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 2.34/2.58  thf(zf_stmt_0, negated_conjecture,
% 2.34/2.58    (~( ![A:$i]:
% 2.34/2.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.34/2.58          ( ![B:$i]:
% 2.34/2.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.34/2.58              ( ![C:$i]:
% 2.34/2.58                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.58                    ( m1_subset_1 @
% 2.34/2.58                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.58                  ( ![D:$i]:
% 2.34/2.58                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.34/2.58                      ( r1_tarski @
% 2.34/2.58                        ( k5_setfam_1 @ A @ D ) @ 
% 2.34/2.58                        ( k5_setfam_1 @
% 2.34/2.58                          A @ 
% 2.34/2.58                          ( k6_funct_2 @
% 2.34/2.58                            A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 2.34/2.58    inference('cnf.neg', [status(esa)], [t184_funct_2])).
% 2.34/2.58  thf('0', plain,
% 2.34/2.58      (~ (r1_tarski @ (k5_setfam_1 @ sk_A @ sk_D) @ 
% 2.34/2.58          (k5_setfam_1 @ sk_A @ 
% 2.34/2.58           (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58            (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D))))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('1', plain,
% 2.34/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf(redefinition_k5_setfam_1, axiom,
% 2.34/2.58    (![A:$i,B:$i]:
% 2.34/2.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.34/2.58       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 2.34/2.58  thf('2', plain,
% 2.34/2.58      (![X8 : $i, X9 : $i]:
% 2.34/2.58         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 2.34/2.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 2.34/2.58      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 2.34/2.58  thf('3', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 2.34/2.58      inference('sup-', [status(thm)], ['1', '2'])).
% 2.34/2.58  thf('4', plain,
% 2.34/2.58      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 2.34/2.58          (k5_setfam_1 @ sk_A @ 
% 2.34/2.58           (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58            (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D))))),
% 2.34/2.58      inference('demod', [status(thm)], ['0', '3'])).
% 2.34/2.58  thf('5', plain,
% 2.34/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('6', plain,
% 2.34/2.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf(dt_k7_funct_2, axiom,
% 2.34/2.58    (![A:$i,B:$i,C:$i,D:$i]:
% 2.34/2.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 2.34/2.58         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.34/2.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 2.34/2.58       ( m1_subset_1 @
% 2.34/2.58         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 2.34/2.58  thf('7', plain,
% 2.34/2.58      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.34/2.58         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 2.34/2.58          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 2.34/2.58          | ~ (v1_funct_1 @ X20)
% 2.34/2.58          | (v1_xboole_0 @ X22)
% 2.34/2.58          | (v1_xboole_0 @ X21)
% 2.34/2.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21)))
% 2.34/2.58          | (m1_subset_1 @ (k7_funct_2 @ X21 @ X22 @ X20 @ X23) @ 
% 2.34/2.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 2.34/2.58      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 2.34/2.58  thf('8', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 2.34/2.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.34/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.34/2.58          | (v1_xboole_0 @ sk_A)
% 2.34/2.58          | (v1_xboole_0 @ sk_B)
% 2.34/2.58          | ~ (v1_funct_1 @ sk_C_1)
% 2.34/2.58          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 2.34/2.58      inference('sup-', [status(thm)], ['6', '7'])).
% 2.34/2.58  thf('9', plain, ((v1_funct_1 @ sk_C_1)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('10', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('11', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 2.34/2.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.34/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.34/2.58          | (v1_xboole_0 @ sk_A)
% 2.34/2.58          | (v1_xboole_0 @ sk_B))),
% 2.34/2.58      inference('demod', [status(thm)], ['8', '9', '10'])).
% 2.34/2.58  thf('12', plain,
% 2.34/2.58      (((v1_xboole_0 @ sk_B)
% 2.34/2.58        | (v1_xboole_0 @ sk_A)
% 2.34/2.58        | (m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 2.34/2.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 2.34/2.58      inference('sup-', [status(thm)], ['5', '11'])).
% 2.34/2.58  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('14', plain,
% 2.34/2.58      (((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 2.34/2.58         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.34/2.58        | (v1_xboole_0 @ sk_A))),
% 2.34/2.58      inference('clc', [status(thm)], ['12', '13'])).
% 2.34/2.58  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('16', plain,
% 2.34/2.58      ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D) @ 
% 2.34/2.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 2.34/2.58      inference('clc', [status(thm)], ['14', '15'])).
% 2.34/2.58  thf('17', plain,
% 2.34/2.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf(dt_k6_funct_2, axiom,
% 2.34/2.58    (![A:$i,B:$i,C:$i,D:$i]:
% 2.34/2.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 2.34/2.58         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.34/2.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 2.34/2.58       ( m1_subset_1 @
% 2.34/2.58         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 2.34/2.58  thf('18', plain,
% 2.34/2.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 2.34/2.58         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 2.34/2.58          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 2.34/2.58          | ~ (v1_funct_1 @ X16)
% 2.34/2.58          | (v1_xboole_0 @ X18)
% 2.34/2.58          | (v1_xboole_0 @ X17)
% 2.34/2.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18)))
% 2.34/2.58          | (m1_subset_1 @ (k6_funct_2 @ X17 @ X18 @ X16 @ X19) @ 
% 2.34/2.58             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X17))))),
% 2.34/2.58      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 2.34/2.58  thf('19', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 2.34/2.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.34/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.34/2.58          | (v1_xboole_0 @ sk_A)
% 2.34/2.58          | (v1_xboole_0 @ sk_B)
% 2.34/2.58          | ~ (v1_funct_1 @ sk_C_1)
% 2.34/2.58          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 2.34/2.58      inference('sup-', [status(thm)], ['17', '18'])).
% 2.34/2.58  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('21', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('22', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0) @ 
% 2.34/2.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.34/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.34/2.58          | (v1_xboole_0 @ sk_A)
% 2.34/2.58          | (v1_xboole_0 @ sk_B))),
% 2.34/2.58      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.34/2.58  thf('23', plain,
% 2.34/2.58      (((v1_xboole_0 @ sk_B)
% 2.34/2.58        | (v1_xboole_0 @ sk_A)
% 2.34/2.58        | (m1_subset_1 @ 
% 2.34/2.58           (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58            (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 2.34/2.58      inference('sup-', [status(thm)], ['16', '22'])).
% 2.34/2.58  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('25', plain,
% 2.34/2.58      (((m1_subset_1 @ 
% 2.34/2.58         (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58          (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.34/2.58        | (v1_xboole_0 @ sk_A))),
% 2.34/2.58      inference('clc', [status(thm)], ['23', '24'])).
% 2.34/2.58  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('27', plain,
% 2.34/2.58      ((m1_subset_1 @ 
% 2.34/2.58        (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58         (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.58      inference('clc', [status(thm)], ['25', '26'])).
% 2.34/2.58  thf('28', plain,
% 2.34/2.58      (![X8 : $i, X9 : $i]:
% 2.34/2.58         (((k5_setfam_1 @ X9 @ X8) = (k3_tarski @ X8))
% 2.34/2.58          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 2.34/2.58      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 2.34/2.58  thf('29', plain,
% 2.34/2.58      (((k5_setfam_1 @ sk_A @ 
% 2.34/2.58         (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58          (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)))
% 2.34/2.58         = (k3_tarski @ 
% 2.34/2.58            (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58             (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D))))),
% 2.34/2.58      inference('sup-', [status(thm)], ['27', '28'])).
% 2.34/2.58  thf('30', plain,
% 2.34/2.58      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 2.34/2.58          (k3_tarski @ 
% 2.34/2.58           (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58            (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D))))),
% 2.34/2.58      inference('demod', [status(thm)], ['4', '29'])).
% 2.34/2.58  thf(t94_zfmisc_1, axiom,
% 2.34/2.58    (![A:$i,B:$i]:
% 2.34/2.58     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 2.34/2.58       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 2.34/2.58  thf('31', plain,
% 2.34/2.58      (![X3 : $i, X4 : $i]:
% 2.34/2.58         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 2.34/2.58          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 2.34/2.58      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 2.34/2.58  thf('32', plain,
% 2.34/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf(t4_subset, axiom,
% 2.34/2.58    (![A:$i,B:$i,C:$i]:
% 2.34/2.58     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.34/2.58       ( m1_subset_1 @ A @ C ) ))).
% 2.34/2.58  thf('33', plain,
% 2.34/2.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.34/2.58         (~ (r2_hidden @ X13 @ X14)
% 2.34/2.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 2.34/2.58          | (m1_subset_1 @ X13 @ X15))),
% 2.34/2.58      inference('cnf', [status(esa)], [t4_subset])).
% 2.34/2.58  thf('34', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_D))),
% 2.34/2.58      inference('sup-', [status(thm)], ['32', '33'])).
% 2.34/2.58  thf('35', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 2.34/2.58          | (m1_subset_1 @ (sk_C @ X0 @ sk_D) @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.58      inference('sup-', [status(thm)], ['31', '34'])).
% 2.34/2.58  thf(t3_subset, axiom,
% 2.34/2.58    (![A:$i,B:$i]:
% 2.34/2.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.34/2.58  thf('36', plain,
% 2.34/2.58      (![X10 : $i, X11 : $i]:
% 2.34/2.58         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 2.34/2.58      inference('cnf', [status(esa)], [t3_subset])).
% 2.34/2.58  thf('37', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 2.34/2.58          | (r1_tarski @ (sk_C @ X0 @ sk_D) @ sk_A))),
% 2.34/2.58      inference('sup-', [status(thm)], ['35', '36'])).
% 2.34/2.58  thf('38', plain,
% 2.34/2.58      (![X3 : $i, X4 : $i]:
% 2.34/2.58         ((r1_tarski @ (k3_tarski @ X3) @ X4)
% 2.34/2.58          | ~ (r1_tarski @ (sk_C @ X4 @ X3) @ X4))),
% 2.34/2.58      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 2.34/2.58  thf('39', plain,
% 2.34/2.58      (((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)
% 2.34/2.58        | (r1_tarski @ (k3_tarski @ sk_D) @ sk_A))),
% 2.34/2.58      inference('sup-', [status(thm)], ['37', '38'])).
% 2.34/2.58  thf('40', plain, ((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)),
% 2.34/2.58      inference('simplify', [status(thm)], ['39'])).
% 2.34/2.58  thf('41', plain,
% 2.34/2.58      (![X10 : $i, X12 : $i]:
% 2.34/2.58         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 2.34/2.58      inference('cnf', [status(esa)], [t3_subset])).
% 2.34/2.58  thf('42', plain, ((m1_subset_1 @ (k3_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 2.34/2.58      inference('sup-', [status(thm)], ['40', '41'])).
% 2.34/2.58  thf('43', plain,
% 2.34/2.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('44', plain,
% 2.34/2.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf(t182_funct_2, axiom,
% 2.34/2.58    (![A:$i]:
% 2.34/2.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.34/2.58       ( ![B:$i]:
% 2.34/2.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.34/2.58           ( ![C:$i]:
% 2.34/2.58             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.34/2.58                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.34/2.58               ( ![D:$i]:
% 2.34/2.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.34/2.58                   ( ![E:$i]:
% 2.34/2.58                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 2.34/2.58                       ( ( m1_setfam_1 @ D @ E ) =>
% 2.34/2.58                         ( m1_setfam_1 @
% 2.34/2.58                           ( k6_funct_2 @
% 2.34/2.58                             A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ 
% 2.34/2.58                           E ) ) ) ) ) ) ) ) ) ) ))).
% 2.34/2.58  thf('45', plain,
% 2.34/2.58      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.34/2.58         ((v1_xboole_0 @ X24)
% 2.34/2.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X26)))
% 2.34/2.58          | ~ (m1_setfam_1 @ X25 @ X27)
% 2.34/2.58          | (m1_setfam_1 @ 
% 2.34/2.58             (k6_funct_2 @ X26 @ X24 @ X28 @ 
% 2.34/2.58              (k7_funct_2 @ X26 @ X24 @ X28 @ X25)) @ 
% 2.34/2.58             X27)
% 2.34/2.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 2.34/2.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 2.34/2.58          | ~ (v1_funct_2 @ X28 @ X26 @ X24)
% 2.34/2.58          | ~ (v1_funct_1 @ X28)
% 2.34/2.58          | (v1_xboole_0 @ X26))),
% 2.34/2.58      inference('cnf', [status(esa)], [t182_funct_2])).
% 2.34/2.58  thf('46', plain,
% 2.34/2.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.58         ((v1_xboole_0 @ sk_A)
% 2.34/2.58          | ~ (v1_funct_1 @ X0)
% 2.34/2.58          | ~ (v1_funct_2 @ X0 @ sk_A @ X1)
% 2.34/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 2.34/2.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_A))
% 2.34/2.58          | (m1_setfam_1 @ 
% 2.34/2.58             (k6_funct_2 @ sk_A @ X1 @ X0 @ 
% 2.34/2.58              (k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D)) @ 
% 2.34/2.58             X2)
% 2.34/2.58          | ~ (m1_setfam_1 @ sk_D @ X2)
% 2.34/2.58          | (v1_xboole_0 @ X1))),
% 2.34/2.58      inference('sup-', [status(thm)], ['44', '45'])).
% 2.34/2.58  thf('47', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((v1_xboole_0 @ sk_B)
% 2.34/2.58          | ~ (m1_setfam_1 @ sk_D @ X0)
% 2.34/2.58          | (m1_setfam_1 @ 
% 2.34/2.58             (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58              (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58             X0)
% 2.34/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 2.34/2.58          | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 2.34/2.58          | ~ (v1_funct_1 @ sk_C_1)
% 2.34/2.58          | (v1_xboole_0 @ sk_A))),
% 2.34/2.58      inference('sup-', [status(thm)], ['43', '46'])).
% 2.34/2.58  thf('48', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('49', plain, ((v1_funct_1 @ sk_C_1)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('50', plain,
% 2.34/2.58      (![X0 : $i]:
% 2.34/2.58         ((v1_xboole_0 @ sk_B)
% 2.34/2.58          | ~ (m1_setfam_1 @ sk_D @ X0)
% 2.34/2.58          | (m1_setfam_1 @ 
% 2.34/2.58             (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58              (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58             X0)
% 2.34/2.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 2.34/2.58          | (v1_xboole_0 @ sk_A))),
% 2.34/2.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.34/2.58  thf('51', plain,
% 2.34/2.58      (((v1_xboole_0 @ sk_A)
% 2.34/2.58        | (m1_setfam_1 @ 
% 2.34/2.58           (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58            (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58           (k3_tarski @ sk_D))
% 2.34/2.58        | ~ (m1_setfam_1 @ sk_D @ (k3_tarski @ sk_D))
% 2.34/2.58        | (v1_xboole_0 @ sk_B))),
% 2.34/2.58      inference('sup-', [status(thm)], ['42', '50'])).
% 2.34/2.58  thf(d10_xboole_0, axiom,
% 2.34/2.58    (![A:$i,B:$i]:
% 2.34/2.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.34/2.58  thf('52', plain,
% 2.34/2.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.34/2.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.34/2.58  thf('53', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.34/2.58      inference('simplify', [status(thm)], ['52'])).
% 2.34/2.58  thf(d12_setfam_1, axiom,
% 2.34/2.58    (![A:$i,B:$i]:
% 2.34/2.58     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 2.34/2.58  thf('54', plain,
% 2.34/2.58      (![X5 : $i, X7 : $i]:
% 2.34/2.58         ((m1_setfam_1 @ X7 @ X5) | ~ (r1_tarski @ X5 @ (k3_tarski @ X7)))),
% 2.34/2.58      inference('cnf', [status(esa)], [d12_setfam_1])).
% 2.34/2.58  thf('55', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 2.34/2.58      inference('sup-', [status(thm)], ['53', '54'])).
% 2.34/2.58  thf('56', plain,
% 2.34/2.58      (((v1_xboole_0 @ sk_A)
% 2.34/2.58        | (m1_setfam_1 @ 
% 2.34/2.58           (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58            (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58           (k3_tarski @ sk_D))
% 2.34/2.58        | (v1_xboole_0 @ sk_B))),
% 2.34/2.58      inference('demod', [status(thm)], ['51', '55'])).
% 2.34/2.58  thf('57', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('58', plain,
% 2.34/2.58      (((v1_xboole_0 @ sk_B)
% 2.34/2.58        | (m1_setfam_1 @ 
% 2.34/2.58           (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58            (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58           (k3_tarski @ sk_D)))),
% 2.34/2.58      inference('clc', [status(thm)], ['56', '57'])).
% 2.34/2.58  thf('59', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.34/2.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.58  thf('60', plain,
% 2.34/2.58      ((m1_setfam_1 @ 
% 2.34/2.58        (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58         (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D)) @ 
% 2.34/2.58        (k3_tarski @ sk_D))),
% 2.34/2.58      inference('clc', [status(thm)], ['58', '59'])).
% 2.34/2.58  thf('61', plain,
% 2.34/2.58      (![X5 : $i, X6 : $i]:
% 2.34/2.58         ((r1_tarski @ X5 @ (k3_tarski @ X6)) | ~ (m1_setfam_1 @ X6 @ X5))),
% 2.34/2.58      inference('cnf', [status(esa)], [d12_setfam_1])).
% 2.34/2.58  thf('62', plain,
% 2.34/2.58      ((r1_tarski @ (k3_tarski @ sk_D) @ 
% 2.34/2.58        (k3_tarski @ 
% 2.34/2.58         (k6_funct_2 @ sk_A @ sk_B @ sk_C_1 @ 
% 2.34/2.58          (k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D))))),
% 2.34/2.58      inference('sup-', [status(thm)], ['60', '61'])).
% 2.34/2.58  thf('63', plain, ($false), inference('demod', [status(thm)], ['30', '62'])).
% 2.34/2.58  
% 2.34/2.58  % SZS output end Refutation
% 2.34/2.58  
% 2.34/2.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

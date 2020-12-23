%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.50FJKZKI2q

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:56 EST 2020

% Result     : Theorem 1.12s
% Output     : Refutation 1.12s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 143 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  954 (2375 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k6_funct_2_type,type,(
    k6_funct_2: $i > $i > $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k5_setfam_1 @ sk_A @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( ( k5_setfam_1 @ X15 @ X14 )
        = ( k3_tarski @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_D )
    = ( k3_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X24 @ X25 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X20 @ X21 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k5_setfam_1 @ X15 @ X14 )
        = ( k3_tarski @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) )
    = ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['4','29'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X9 ) @ X10 )
      | ( r2_hidden @ ( sk_C_2 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r1_tarski @ X7 @ X5 )
      | ( X6
       != ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('39',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( r1_tarski @ ( sk_C_2 @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X9 ) @ X10 )
      | ~ ( r1_tarski @ ( sk_C_2 @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('42',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A )
    | ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X29 ) ) )
      | ~ ( m1_setfam_1 @ X28 @ X30 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ X29 @ X27 @ X31 @ ( k7_funct_2 @ X29 @ X27 @ X31 @ X28 ) ) @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X27 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t182_funct_2])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ X1 @ X0 @ ( k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D ) ) @ X2 )
      | ~ ( m1_setfam_1 @ sk_D @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ~ ( m1_setfam_1 @ sk_D @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('59',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_setfam_1 @ X13 @ X11 )
      | ~ ( r1_tarski @ X11 @ ( k3_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['54','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ ( k3_tarski @ X12 ) )
      | ~ ( m1_setfam_1 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('67',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['30','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.50FJKZKI2q
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.12/1.33  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.12/1.33  % Solved by: fo/fo7.sh
% 1.12/1.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.12/1.33  % done 934 iterations in 0.874s
% 1.12/1.33  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.12/1.33  % SZS output start Refutation
% 1.12/1.33  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.12/1.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.12/1.33  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.12/1.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.12/1.33  thf(sk_D_type, type, sk_D: $i).
% 1.12/1.33  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.12/1.33  thf(sk_A_type, type, sk_A: $i).
% 1.12/1.33  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.12/1.33  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 1.12/1.33  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.12/1.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.12/1.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.12/1.33  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.12/1.33  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 1.12/1.33  thf(sk_B_type, type, sk_B: $i).
% 1.12/1.33  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 1.12/1.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.12/1.33  thf(sk_C_3_type, type, sk_C_3: $i).
% 1.12/1.33  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 1.12/1.33  thf(t184_funct_2, conjecture,
% 1.12/1.33    (![A:$i]:
% 1.12/1.33     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.12/1.33       ( ![B:$i]:
% 1.12/1.33         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.12/1.33           ( ![C:$i]:
% 1.12/1.33             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.12/1.33                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.12/1.33               ( ![D:$i]:
% 1.12/1.33                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.12/1.33                   ( r1_tarski @
% 1.12/1.33                     ( k5_setfam_1 @ A @ D ) @ 
% 1.12/1.33                     ( k5_setfam_1 @
% 1.12/1.33                       A @ 
% 1.12/1.33                       ( k6_funct_2 @
% 1.12/1.33                         A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.33  thf(zf_stmt_0, negated_conjecture,
% 1.12/1.33    (~( ![A:$i]:
% 1.12/1.33        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.12/1.33          ( ![B:$i]:
% 1.12/1.33            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.12/1.33              ( ![C:$i]:
% 1.12/1.33                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.12/1.33                    ( m1_subset_1 @
% 1.12/1.33                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.12/1.33                  ( ![D:$i]:
% 1.12/1.33                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.12/1.33                      ( r1_tarski @
% 1.12/1.33                        ( k5_setfam_1 @ A @ D ) @ 
% 1.12/1.33                        ( k5_setfam_1 @
% 1.12/1.33                          A @ 
% 1.12/1.33                          ( k6_funct_2 @
% 1.12/1.33                            A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 1.12/1.33    inference('cnf.neg', [status(esa)], [t184_funct_2])).
% 1.12/1.33  thf('0', plain,
% 1.12/1.33      (~ (r1_tarski @ (k5_setfam_1 @ sk_A @ sk_D) @ 
% 1.12/1.33          (k5_setfam_1 @ sk_A @ 
% 1.12/1.33           (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33            (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D))))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('1', plain,
% 1.12/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf(redefinition_k5_setfam_1, axiom,
% 1.12/1.33    (![A:$i,B:$i]:
% 1.12/1.33     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.12/1.33       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 1.12/1.33  thf('2', plain,
% 1.12/1.33      (![X14 : $i, X15 : $i]:
% 1.12/1.33         (((k5_setfam_1 @ X15 @ X14) = (k3_tarski @ X14))
% 1.12/1.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 1.12/1.33      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.12/1.33  thf('3', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 1.12/1.33      inference('sup-', [status(thm)], ['1', '2'])).
% 1.12/1.33  thf('4', plain,
% 1.12/1.33      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 1.12/1.33          (k5_setfam_1 @ sk_A @ 
% 1.12/1.33           (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33            (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D))))),
% 1.12/1.33      inference('demod', [status(thm)], ['0', '3'])).
% 1.12/1.33  thf('5', plain,
% 1.12/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('6', plain,
% 1.12/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf(dt_k7_funct_2, axiom,
% 1.12/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.12/1.33     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.12/1.33         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.12/1.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.12/1.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 1.12/1.33       ( m1_subset_1 @
% 1.12/1.33         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 1.12/1.33  thf('7', plain,
% 1.12/1.33      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.12/1.33         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.12/1.33          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 1.12/1.33          | ~ (v1_funct_1 @ X23)
% 1.12/1.33          | (v1_xboole_0 @ X25)
% 1.12/1.33          | (v1_xboole_0 @ X24)
% 1.12/1.33          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24)))
% 1.12/1.33          | (m1_subset_1 @ (k7_funct_2 @ X24 @ X25 @ X23 @ X26) @ 
% 1.12/1.33             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 1.12/1.33      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 1.12/1.33  thf('8', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0) @ 
% 1.12/1.33           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.12/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.12/1.33          | (v1_xboole_0 @ sk_A)
% 1.12/1.33          | (v1_xboole_0 @ sk_B)
% 1.12/1.33          | ~ (v1_funct_1 @ sk_C_3)
% 1.12/1.33          | ~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B))),
% 1.12/1.33      inference('sup-', [status(thm)], ['6', '7'])).
% 1.12/1.33  thf('9', plain, ((v1_funct_1 @ sk_C_3)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('10', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('11', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0) @ 
% 1.12/1.33           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.12/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.12/1.33          | (v1_xboole_0 @ sk_A)
% 1.12/1.33          | (v1_xboole_0 @ sk_B))),
% 1.12/1.33      inference('demod', [status(thm)], ['8', '9', '10'])).
% 1.12/1.33  thf('12', plain,
% 1.12/1.33      (((v1_xboole_0 @ sk_B)
% 1.12/1.33        | (v1_xboole_0 @ sk_A)
% 1.12/1.33        | (m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D) @ 
% 1.12/1.33           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 1.12/1.33      inference('sup-', [status(thm)], ['5', '11'])).
% 1.12/1.33  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('14', plain,
% 1.12/1.33      (((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D) @ 
% 1.12/1.33         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.12/1.33        | (v1_xboole_0 @ sk_A))),
% 1.12/1.33      inference('clc', [status(thm)], ['12', '13'])).
% 1.12/1.33  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('16', plain,
% 1.12/1.33      ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D) @ 
% 1.12/1.33        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 1.12/1.33      inference('clc', [status(thm)], ['14', '15'])).
% 1.12/1.33  thf('17', plain,
% 1.12/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf(dt_k6_funct_2, axiom,
% 1.12/1.33    (![A:$i,B:$i,C:$i,D:$i]:
% 1.12/1.33     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.12/1.33         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.12/1.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.12/1.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 1.12/1.33       ( m1_subset_1 @
% 1.12/1.33         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.12/1.33  thf('18', plain,
% 1.12/1.33      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.12/1.33         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.12/1.33          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 1.12/1.33          | ~ (v1_funct_1 @ X19)
% 1.12/1.33          | (v1_xboole_0 @ X21)
% 1.12/1.33          | (v1_xboole_0 @ X20)
% 1.12/1.33          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21)))
% 1.12/1.33          | (m1_subset_1 @ (k6_funct_2 @ X20 @ X21 @ X19 @ X22) @ 
% 1.12/1.33             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 1.12/1.33      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 1.12/1.33  thf('19', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0) @ 
% 1.12/1.33           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.12/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.12/1.33          | (v1_xboole_0 @ sk_A)
% 1.12/1.33          | (v1_xboole_0 @ sk_B)
% 1.12/1.33          | ~ (v1_funct_1 @ sk_C_3)
% 1.12/1.33          | ~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B))),
% 1.12/1.33      inference('sup-', [status(thm)], ['17', '18'])).
% 1.12/1.33  thf('20', plain, ((v1_funct_1 @ sk_C_3)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('21', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('22', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ X0) @ 
% 1.12/1.33           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.12/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 1.12/1.33          | (v1_xboole_0 @ sk_A)
% 1.12/1.33          | (v1_xboole_0 @ sk_B))),
% 1.12/1.33      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.12/1.33  thf('23', plain,
% 1.12/1.33      (((v1_xboole_0 @ sk_B)
% 1.12/1.33        | (v1_xboole_0 @ sk_A)
% 1.12/1.33        | (m1_subset_1 @ 
% 1.12/1.33           (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33            (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 1.12/1.33      inference('sup-', [status(thm)], ['16', '22'])).
% 1.12/1.33  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('25', plain,
% 1.12/1.33      (((m1_subset_1 @ 
% 1.12/1.33         (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33          (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 1.12/1.33        | (v1_xboole_0 @ sk_A))),
% 1.12/1.33      inference('clc', [status(thm)], ['23', '24'])).
% 1.12/1.33  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('27', plain,
% 1.12/1.33      ((m1_subset_1 @ 
% 1.12/1.33        (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33         (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.12/1.33      inference('clc', [status(thm)], ['25', '26'])).
% 1.12/1.33  thf('28', plain,
% 1.12/1.33      (![X14 : $i, X15 : $i]:
% 1.12/1.33         (((k5_setfam_1 @ X15 @ X14) = (k3_tarski @ X14))
% 1.12/1.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 1.12/1.33      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 1.12/1.33  thf('29', plain,
% 1.12/1.33      (((k5_setfam_1 @ sk_A @ 
% 1.12/1.33         (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33          (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)))
% 1.12/1.33         = (k3_tarski @ 
% 1.12/1.33            (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33             (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D))))),
% 1.12/1.33      inference('sup-', [status(thm)], ['27', '28'])).
% 1.12/1.33  thf('30', plain,
% 1.12/1.33      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 1.12/1.33          (k3_tarski @ 
% 1.12/1.33           (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33            (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D))))),
% 1.12/1.33      inference('demod', [status(thm)], ['4', '29'])).
% 1.12/1.33  thf(t94_zfmisc_1, axiom,
% 1.12/1.33    (![A:$i,B:$i]:
% 1.12/1.33     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 1.12/1.33       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 1.12/1.33  thf('31', plain,
% 1.12/1.33      (![X9 : $i, X10 : $i]:
% 1.12/1.33         ((r1_tarski @ (k3_tarski @ X9) @ X10)
% 1.12/1.33          | (r2_hidden @ (sk_C_2 @ X10 @ X9) @ X9))),
% 1.12/1.33      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 1.12/1.33  thf('32', plain,
% 1.12/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf(t3_subset, axiom,
% 1.12/1.33    (![A:$i,B:$i]:
% 1.12/1.33     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.12/1.33  thf('33', plain,
% 1.12/1.33      (![X16 : $i, X17 : $i]:
% 1.12/1.33         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.12/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.12/1.33  thf('34', plain, ((r1_tarski @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.12/1.33      inference('sup-', [status(thm)], ['32', '33'])).
% 1.12/1.33  thf(d3_tarski, axiom,
% 1.12/1.33    (![A:$i,B:$i]:
% 1.12/1.33     ( ( r1_tarski @ A @ B ) <=>
% 1.12/1.33       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.12/1.33  thf('35', plain,
% 1.12/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.33         (~ (r2_hidden @ X0 @ X1)
% 1.12/1.33          | (r2_hidden @ X0 @ X2)
% 1.12/1.33          | ~ (r1_tarski @ X1 @ X2))),
% 1.12/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.12/1.33  thf('36', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_D))),
% 1.12/1.33      inference('sup-', [status(thm)], ['34', '35'])).
% 1.12/1.33  thf('37', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 1.12/1.33          | (r2_hidden @ (sk_C_2 @ X0 @ sk_D) @ (k1_zfmisc_1 @ sk_A)))),
% 1.12/1.33      inference('sup-', [status(thm)], ['31', '36'])).
% 1.12/1.33  thf(d1_zfmisc_1, axiom,
% 1.12/1.33    (![A:$i,B:$i]:
% 1.12/1.33     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.12/1.33       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.12/1.33  thf('38', plain,
% 1.12/1.33      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.12/1.33         (~ (r2_hidden @ X7 @ X6)
% 1.12/1.33          | (r1_tarski @ X7 @ X5)
% 1.12/1.33          | ((X6) != (k1_zfmisc_1 @ X5)))),
% 1.12/1.33      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.12/1.33  thf('39', plain,
% 1.12/1.33      (![X5 : $i, X7 : $i]:
% 1.12/1.33         ((r1_tarski @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k1_zfmisc_1 @ X5)))),
% 1.12/1.33      inference('simplify', [status(thm)], ['38'])).
% 1.12/1.33  thf('40', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 1.12/1.33          | (r1_tarski @ (sk_C_2 @ X0 @ sk_D) @ sk_A))),
% 1.12/1.33      inference('sup-', [status(thm)], ['37', '39'])).
% 1.12/1.33  thf('41', plain,
% 1.12/1.33      (![X9 : $i, X10 : $i]:
% 1.12/1.33         ((r1_tarski @ (k3_tarski @ X9) @ X10)
% 1.12/1.33          | ~ (r1_tarski @ (sk_C_2 @ X10 @ X9) @ X10))),
% 1.12/1.33      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 1.12/1.33  thf('42', plain,
% 1.12/1.33      (((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)
% 1.12/1.33        | (r1_tarski @ (k3_tarski @ sk_D) @ sk_A))),
% 1.12/1.33      inference('sup-', [status(thm)], ['40', '41'])).
% 1.12/1.33  thf('43', plain, ((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)),
% 1.12/1.33      inference('simplify', [status(thm)], ['42'])).
% 1.12/1.33  thf('44', plain,
% 1.12/1.33      (![X16 : $i, X18 : $i]:
% 1.12/1.33         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 1.12/1.33      inference('cnf', [status(esa)], [t3_subset])).
% 1.12/1.33  thf('45', plain, ((m1_subset_1 @ (k3_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 1.12/1.33      inference('sup-', [status(thm)], ['43', '44'])).
% 1.12/1.33  thf('46', plain,
% 1.12/1.33      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('47', plain,
% 1.12/1.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf(t182_funct_2, axiom,
% 1.12/1.33    (![A:$i]:
% 1.12/1.33     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.12/1.33       ( ![B:$i]:
% 1.12/1.33         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.12/1.33           ( ![C:$i]:
% 1.12/1.33             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.12/1.33                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.12/1.33               ( ![D:$i]:
% 1.12/1.33                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.12/1.33                   ( ![E:$i]:
% 1.12/1.33                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 1.12/1.33                       ( ( m1_setfam_1 @ D @ E ) =>
% 1.12/1.33                         ( m1_setfam_1 @
% 1.12/1.33                           ( k6_funct_2 @
% 1.12/1.33                             A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ 
% 1.12/1.33                           E ) ) ) ) ) ) ) ) ) ) ))).
% 1.12/1.33  thf('48', plain,
% 1.12/1.33      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.12/1.33         ((v1_xboole_0 @ X27)
% 1.12/1.33          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X29)))
% 1.12/1.33          | ~ (m1_setfam_1 @ X28 @ X30)
% 1.12/1.33          | (m1_setfam_1 @ 
% 1.12/1.33             (k6_funct_2 @ X29 @ X27 @ X31 @ 
% 1.12/1.33              (k7_funct_2 @ X29 @ X27 @ X31 @ X28)) @ 
% 1.12/1.33             X30)
% 1.12/1.33          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 1.12/1.33          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X27)))
% 1.12/1.33          | ~ (v1_funct_2 @ X31 @ X29 @ X27)
% 1.12/1.33          | ~ (v1_funct_1 @ X31)
% 1.12/1.33          | (v1_xboole_0 @ X29))),
% 1.12/1.33      inference('cnf', [status(esa)], [t182_funct_2])).
% 1.12/1.33  thf('49', plain,
% 1.12/1.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.12/1.33         ((v1_xboole_0 @ sk_A)
% 1.12/1.33          | ~ (v1_funct_1 @ X0)
% 1.12/1.33          | ~ (v1_funct_2 @ X0 @ sk_A @ X1)
% 1.12/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 1.12/1.33          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_A))
% 1.12/1.33          | (m1_setfam_1 @ 
% 1.12/1.33             (k6_funct_2 @ sk_A @ X1 @ X0 @ 
% 1.12/1.33              (k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D)) @ 
% 1.12/1.33             X2)
% 1.12/1.33          | ~ (m1_setfam_1 @ sk_D @ X2)
% 1.12/1.33          | (v1_xboole_0 @ X1))),
% 1.12/1.33      inference('sup-', [status(thm)], ['47', '48'])).
% 1.12/1.33  thf('50', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((v1_xboole_0 @ sk_B)
% 1.12/1.33          | ~ (m1_setfam_1 @ sk_D @ X0)
% 1.12/1.33          | (m1_setfam_1 @ 
% 1.12/1.33             (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33              (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33             X0)
% 1.12/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.12/1.33          | ~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)
% 1.12/1.33          | ~ (v1_funct_1 @ sk_C_3)
% 1.12/1.33          | (v1_xboole_0 @ sk_A))),
% 1.12/1.33      inference('sup-', [status(thm)], ['46', '49'])).
% 1.12/1.33  thf('51', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('52', plain, ((v1_funct_1 @ sk_C_3)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('53', plain,
% 1.12/1.33      (![X0 : $i]:
% 1.12/1.33         ((v1_xboole_0 @ sk_B)
% 1.12/1.33          | ~ (m1_setfam_1 @ sk_D @ X0)
% 1.12/1.33          | (m1_setfam_1 @ 
% 1.12/1.33             (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33              (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33             X0)
% 1.12/1.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 1.12/1.33          | (v1_xboole_0 @ sk_A))),
% 1.12/1.33      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.12/1.33  thf('54', plain,
% 1.12/1.33      (((v1_xboole_0 @ sk_A)
% 1.12/1.33        | (m1_setfam_1 @ 
% 1.12/1.33           (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33            (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33           (k3_tarski @ sk_D))
% 1.12/1.33        | ~ (m1_setfam_1 @ sk_D @ (k3_tarski @ sk_D))
% 1.12/1.33        | (v1_xboole_0 @ sk_B))),
% 1.12/1.33      inference('sup-', [status(thm)], ['45', '53'])).
% 1.12/1.33  thf('55', plain,
% 1.12/1.33      (![X1 : $i, X3 : $i]:
% 1.12/1.33         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.12/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.12/1.33  thf('56', plain,
% 1.12/1.33      (![X1 : $i, X3 : $i]:
% 1.12/1.33         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.12/1.33      inference('cnf', [status(esa)], [d3_tarski])).
% 1.12/1.33  thf('57', plain,
% 1.12/1.33      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.12/1.33      inference('sup-', [status(thm)], ['55', '56'])).
% 1.12/1.33  thf('58', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.12/1.33      inference('simplify', [status(thm)], ['57'])).
% 1.12/1.33  thf(d12_setfam_1, axiom,
% 1.12/1.33    (![A:$i,B:$i]:
% 1.12/1.33     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 1.12/1.33  thf('59', plain,
% 1.12/1.33      (![X11 : $i, X13 : $i]:
% 1.12/1.33         ((m1_setfam_1 @ X13 @ X11) | ~ (r1_tarski @ X11 @ (k3_tarski @ X13)))),
% 1.12/1.33      inference('cnf', [status(esa)], [d12_setfam_1])).
% 1.12/1.33  thf('60', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 1.12/1.33      inference('sup-', [status(thm)], ['58', '59'])).
% 1.12/1.33  thf('61', plain,
% 1.12/1.33      (((v1_xboole_0 @ sk_A)
% 1.12/1.33        | (m1_setfam_1 @ 
% 1.12/1.33           (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33            (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33           (k3_tarski @ sk_D))
% 1.12/1.33        | (v1_xboole_0 @ sk_B))),
% 1.12/1.33      inference('demod', [status(thm)], ['54', '60'])).
% 1.12/1.33  thf('62', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('63', plain,
% 1.12/1.33      (((v1_xboole_0 @ sk_B)
% 1.12/1.33        | (m1_setfam_1 @ 
% 1.12/1.33           (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33            (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33           (k3_tarski @ sk_D)))),
% 1.12/1.33      inference('clc', [status(thm)], ['61', '62'])).
% 1.12/1.33  thf('64', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.12/1.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.12/1.33  thf('65', plain,
% 1.12/1.33      ((m1_setfam_1 @ 
% 1.12/1.33        (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33         (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D)) @ 
% 1.12/1.33        (k3_tarski @ sk_D))),
% 1.12/1.33      inference('clc', [status(thm)], ['63', '64'])).
% 1.12/1.33  thf('66', plain,
% 1.12/1.33      (![X11 : $i, X12 : $i]:
% 1.12/1.33         ((r1_tarski @ X11 @ (k3_tarski @ X12)) | ~ (m1_setfam_1 @ X12 @ X11))),
% 1.12/1.33      inference('cnf', [status(esa)], [d12_setfam_1])).
% 1.12/1.33  thf('67', plain,
% 1.12/1.33      ((r1_tarski @ (k3_tarski @ sk_D) @ 
% 1.12/1.33        (k3_tarski @ 
% 1.12/1.33         (k6_funct_2 @ sk_A @ sk_B @ sk_C_3 @ 
% 1.12/1.33          (k7_funct_2 @ sk_A @ sk_B @ sk_C_3 @ sk_D))))),
% 1.12/1.33      inference('sup-', [status(thm)], ['65', '66'])).
% 1.12/1.33  thf('68', plain, ($false), inference('demod', [status(thm)], ['30', '67'])).
% 1.12/1.33  
% 1.12/1.33  % SZS output end Refutation
% 1.12/1.33  
% 1.12/1.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

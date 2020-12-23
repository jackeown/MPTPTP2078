%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GL63Tbc35V

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:37 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 119 expanded)
%              Number of leaves         :   31 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  526 (1029 expanded)
%              Number of equality atoms :   35 (  62 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t2_yellow19,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
           => ! [C: $i] :
                ~ ( ( r2_hidden @ C @ B )
                  & ( v1_xboole_0 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow19])).

thf('0',plain,(
    v1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    v1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_3 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('10',plain,(
    ! [X15: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X8 @ X9 ) @ X9 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('14',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X8 @ X9 ) @ X9 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k9_setfam_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) @ ( k9_setfam_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k9_setfam_1 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 )
    | ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('23',plain,(
    v13_waybel_0 @ sk_B_1 @ ( k2_yellow_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t11_waybel_7,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) )
     => ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
      <=> ! [C: $i,D: $i] :
            ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ D @ A )
              & ( r2_hidden @ C @ B ) )
           => ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( v13_waybel_0 @ X18 @ ( k3_yellow_1 @ X19 ) )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( r2_hidden @ X21 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ X19 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_waybel_7])).

thf('25',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( k3_yellow_1 @ X17 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('27',plain,(
    ! [X15: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( v13_waybel_0 @ X18 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X19 ) ) )
      | ~ ( r2_hidden @ X20 @ X18 )
      | ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( r2_hidden @ X21 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k9_setfam_1 @ ( k9_setfam_1 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k9_setfam_1 @ sk_A )
        = sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( ( k9_setfam_1 @ sk_A )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,(
    v1_xboole_0 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 @ ( k9_setfam_1 @ sk_A ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('39',plain,(
    ! [X14: $i] :
      ( ( k9_setfam_1 @ X14 )
      = ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k9_setfam_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k9_setfam_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('43',plain,
    ( ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 )
    | ( ( k9_setfam_1 @ sk_A )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k9_setfam_1 @ sk_A )
    = sk_B_1 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v1_subset_1 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['3','44'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('46',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X10 ) @ X10 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('47',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('48',plain,(
    ! [X10: $i] :
      ~ ( v1_subset_1 @ X10 @ X10 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference('sup-',[status(thm)],['45','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GL63Tbc35V
% 0.15/0.38  % Computer   : n008.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 11:31:00 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.24/0.39  % Running in FO mode
% 0.35/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.59  % Solved by: fo/fo7.sh
% 0.35/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.59  % done 133 iterations in 0.095s
% 0.35/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.59  % SZS output start Refutation
% 0.35/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.59  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.35/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.59  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.35/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.59  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.35/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.59  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.35/0.59  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.35/0.59  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.35/0.59  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.35/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.59  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.35/0.59  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.35/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.59  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.35/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.59  thf(t2_yellow19, conjecture,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.59       ( ![B:$i]:
% 0.35/0.59         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.59             ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.35/0.59             ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.35/0.59             ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.35/0.59             ( m1_subset_1 @
% 0.35/0.59               B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.35/0.59           ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ))).
% 0.35/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.59    (~( ![A:$i]:
% 0.35/0.59        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.59          ( ![B:$i]:
% 0.35/0.59            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.59                ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) & 
% 0.35/0.59                ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.35/0.59                ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) & 
% 0.35/0.59                ( m1_subset_1 @
% 0.35/0.59                  B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) ) =>
% 0.35/0.59              ( ![C:$i]: ( ~( ( r2_hidden @ C @ B ) & ( v1_xboole_0 @ C ) ) ) ) ) ) ) )),
% 0.35/0.59    inference('cnf.neg', [status(esa)], [t2_yellow19])).
% 0.35/0.59  thf('0', plain,
% 0.35/0.59      ((v1_subset_1 @ sk_B_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A)))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(t4_yellow_1, axiom,
% 0.35/0.59    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.35/0.59  thf('1', plain,
% 0.35/0.59      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k2_yellow_1 @ (k9_setfam_1 @ X17)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.35/0.59  thf(t1_yellow_1, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.35/0.59       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.35/0.59  thf('2', plain, (![X15 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X15)) = (X15))),
% 0.35/0.59      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.35/0.59  thf('3', plain, ((v1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A))),
% 0.35/0.59      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.35/0.59  thf('4', plain, ((r2_hidden @ sk_C_3 @ sk_B_1)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf(d3_tarski, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.59  thf('5', plain,
% 0.35/0.59      (![X4 : $i, X6 : $i]:
% 0.35/0.59         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.35/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.59  thf(d1_xboole_0, axiom,
% 0.35/0.59    (![A:$i]:
% 0.35/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.59  thf('6', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.59  thf('7', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.35/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.59  thf('8', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ sk_A))))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('9', plain,
% 0.35/0.59      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k2_yellow_1 @ (k9_setfam_1 @ X17)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.35/0.59  thf('10', plain,
% 0.35/0.59      (![X15 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X15)) = (X15))),
% 0.35/0.59      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.35/0.59  thf(redefinition_k9_setfam_1, axiom,
% 0.35/0.59    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.59  thf('11', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.35/0.59  thf('12', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.35/0.59      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.35/0.59  thf(t49_subset_1, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.59       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.35/0.59         ( ( A ) = ( B ) ) ) ))).
% 0.35/0.59  thf('13', plain,
% 0.35/0.59      (![X8 : $i, X9 : $i]:
% 0.35/0.59         ((m1_subset_1 @ (sk_C_1 @ X8 @ X9) @ X9)
% 0.35/0.59          | ((X9) = (X8))
% 0.35/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.35/0.59  thf('14', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.35/0.59  thf('15', plain,
% 0.35/0.59      (![X8 : $i, X9 : $i]:
% 0.35/0.59         ((m1_subset_1 @ (sk_C_1 @ X8 @ X9) @ X9)
% 0.35/0.59          | ((X9) = (X8))
% 0.35/0.59          | ~ (m1_subset_1 @ X8 @ (k9_setfam_1 @ X9)))),
% 0.35/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.35/0.59  thf('16', plain,
% 0.35/0.59      ((((k9_setfam_1 @ sk_A) = (sk_B_1))
% 0.35/0.59        | (m1_subset_1 @ (sk_C_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)) @ 
% 0.35/0.59           (k9_setfam_1 @ sk_A)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['12', '15'])).
% 0.35/0.59  thf(t3_subset, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.59  thf('17', plain,
% 0.35/0.59      (![X11 : $i, X12 : $i]:
% 0.35/0.59         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.59  thf('18', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.35/0.59  thf('19', plain,
% 0.35/0.59      (![X11 : $i, X12 : $i]:
% 0.35/0.59         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k9_setfam_1 @ X12)))),
% 0.35/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.35/0.59  thf('20', plain,
% 0.35/0.59      ((((k9_setfam_1 @ sk_A) = (sk_B_1))
% 0.35/0.59        | (r1_tarski @ (sk_C_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)) @ sk_A))),
% 0.35/0.59      inference('sup-', [status(thm)], ['16', '19'])).
% 0.35/0.59  thf('21', plain, ((v13_waybel_0 @ sk_B_1 @ (k3_yellow_1 @ sk_A))),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('22', plain,
% 0.35/0.59      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k2_yellow_1 @ (k9_setfam_1 @ X17)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.35/0.59  thf('23', plain,
% 0.35/0.59      ((v13_waybel_0 @ sk_B_1 @ (k2_yellow_1 @ (k9_setfam_1 @ sk_A)))),
% 0.35/0.59      inference('demod', [status(thm)], ['21', '22'])).
% 0.35/0.59  thf(t11_waybel_7, axiom,
% 0.35/0.59    (![A:$i,B:$i]:
% 0.35/0.59     ( ( m1_subset_1 @
% 0.35/0.59         B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) =>
% 0.35/0.59       ( ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) ) <=>
% 0.35/0.59         ( ![C:$i,D:$i]:
% 0.35/0.59           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ D @ A ) & 
% 0.35/0.59               ( r2_hidden @ C @ B ) ) =>
% 0.35/0.59             ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.59  thf('24', plain,
% 0.35/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.59         (~ (v13_waybel_0 @ X18 @ (k3_yellow_1 @ X19))
% 0.35/0.59          | ~ (r2_hidden @ X20 @ X18)
% 0.35/0.59          | ~ (r1_tarski @ X20 @ X21)
% 0.35/0.59          | ~ (r1_tarski @ X21 @ X19)
% 0.35/0.59          | (r2_hidden @ X21 @ X18)
% 0.35/0.59          | ~ (m1_subset_1 @ X18 @ 
% 0.35/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ (k3_yellow_1 @ X19)))))),
% 0.35/0.59      inference('cnf', [status(esa)], [t11_waybel_7])).
% 0.35/0.59  thf('25', plain,
% 0.35/0.59      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k2_yellow_1 @ (k9_setfam_1 @ X17)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.35/0.59  thf('26', plain,
% 0.35/0.59      (![X17 : $i]: ((k3_yellow_1 @ X17) = (k2_yellow_1 @ (k9_setfam_1 @ X17)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.35/0.59  thf('27', plain,
% 0.35/0.59      (![X15 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X15)) = (X15))),
% 0.35/0.59      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.35/0.59  thf('28', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.35/0.59  thf('29', plain,
% 0.35/0.59      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.35/0.59         (~ (v13_waybel_0 @ X18 @ (k2_yellow_1 @ (k9_setfam_1 @ X19)))
% 0.35/0.59          | ~ (r2_hidden @ X20 @ X18)
% 0.35/0.59          | ~ (r1_tarski @ X20 @ X21)
% 0.35/0.59          | ~ (r1_tarski @ X21 @ X19)
% 0.35/0.59          | (r2_hidden @ X21 @ X18)
% 0.35/0.59          | ~ (m1_subset_1 @ X18 @ (k9_setfam_1 @ (k9_setfam_1 @ X19))))),
% 0.35/0.59      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.35/0.59  thf('30', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         (~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))
% 0.35/0.59          | (r2_hidden @ X0 @ sk_B_1)
% 0.35/0.59          | ~ (r1_tarski @ X0 @ sk_A)
% 0.35/0.59          | ~ (r1_tarski @ X1 @ X0)
% 0.35/0.59          | ~ (r2_hidden @ X1 @ sk_B_1))),
% 0.35/0.59      inference('sup-', [status(thm)], ['23', '29'])).
% 0.35/0.59  thf('31', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.35/0.59      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.35/0.59  thf('32', plain,
% 0.35/0.59      (![X0 : $i, X1 : $i]:
% 0.35/0.59         ((r2_hidden @ X0 @ sk_B_1)
% 0.35/0.59          | ~ (r1_tarski @ X0 @ sk_A)
% 0.35/0.59          | ~ (r1_tarski @ X1 @ X0)
% 0.35/0.59          | ~ (r2_hidden @ X1 @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.35/0.59  thf('33', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (((k9_setfam_1 @ sk_A) = (sk_B_1))
% 0.35/0.59          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.35/0.59          | ~ (r1_tarski @ X0 @ (sk_C_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)))
% 0.35/0.59          | (r2_hidden @ (sk_C_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1))),
% 0.35/0.59      inference('sup-', [status(thm)], ['20', '32'])).
% 0.35/0.59  thf('34', plain,
% 0.35/0.59      (![X0 : $i]:
% 0.35/0.59         (~ (v1_xboole_0 @ X0)
% 0.35/0.59          | (r2_hidden @ (sk_C_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1)
% 0.35/0.59          | ~ (r2_hidden @ X0 @ sk_B_1)
% 0.35/0.59          | ((k9_setfam_1 @ sk_A) = (sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['7', '33'])).
% 0.35/0.59  thf('35', plain,
% 0.35/0.59      ((((k9_setfam_1 @ sk_A) = (sk_B_1))
% 0.35/0.59        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1)
% 0.35/0.59        | ~ (v1_xboole_0 @ sk_C_3))),
% 0.35/0.59      inference('sup-', [status(thm)], ['4', '34'])).
% 0.35/0.59  thf('36', plain, ((v1_xboole_0 @ sk_C_3)),
% 0.35/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.59  thf('37', plain,
% 0.35/0.59      ((((k9_setfam_1 @ sk_A) = (sk_B_1))
% 0.35/0.59        | (r2_hidden @ (sk_C_1 @ sk_B_1 @ (k9_setfam_1 @ sk_A)) @ sk_B_1))),
% 0.35/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.35/0.59  thf('38', plain,
% 0.35/0.59      (![X8 : $i, X9 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.35/0.59          | ((X9) = (X8))
% 0.35/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.35/0.59      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.35/0.59  thf('39', plain, (![X14 : $i]: ((k9_setfam_1 @ X14) = (k1_zfmisc_1 @ X14))),
% 0.35/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.35/0.59  thf('40', plain,
% 0.35/0.59      (![X8 : $i, X9 : $i]:
% 0.35/0.59         (~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.35/0.59          | ((X9) = (X8))
% 0.35/0.59          | ~ (m1_subset_1 @ X8 @ (k9_setfam_1 @ X9)))),
% 0.35/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.59  thf('41', plain,
% 0.35/0.59      ((((k9_setfam_1 @ sk_A) = (sk_B_1))
% 0.35/0.59        | ~ (m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))
% 0.35/0.59        | ((k9_setfam_1 @ sk_A) = (sk_B_1)))),
% 0.35/0.59      inference('sup-', [status(thm)], ['37', '40'])).
% 0.35/0.59  thf('42', plain,
% 0.35/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k9_setfam_1 @ sk_A)))),
% 0.35/0.59      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.35/0.59  thf('43', plain,
% 0.35/0.59      ((((k9_setfam_1 @ sk_A) = (sk_B_1)) | ((k9_setfam_1 @ sk_A) = (sk_B_1)))),
% 0.35/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.35/0.59  thf('44', plain, (((k9_setfam_1 @ sk_A) = (sk_B_1))),
% 0.35/0.59      inference('simplify', [status(thm)], ['43'])).
% 0.35/0.59  thf('45', plain, ((v1_subset_1 @ sk_B_1 @ sk_B_1)),
% 0.35/0.59      inference('demod', [status(thm)], ['3', '44'])).
% 0.35/0.59  thf(fc14_subset_1, axiom,
% 0.35/0.59    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.35/0.59  thf('46', plain, (![X10 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X10) @ X10)),
% 0.35/0.59      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.35/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.59  thf('47', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.35/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.59  thf('48', plain, (![X10 : $i]: ~ (v1_subset_1 @ X10 @ X10)),
% 0.35/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.59  thf('49', plain, ($false), inference('sup-', [status(thm)], ['45', '48'])).
% 0.35/0.59  
% 0.35/0.59  % SZS output end Refutation
% 0.35/0.59  
% 0.35/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gsI6isHddT

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:48 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 166 expanded)
%              Number of leaves         :   38 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  552 (2067 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t38_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( v3_pre_topc @ C @ A ) )
               => ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v3_pre_topc @ B @ A )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_tops_1])).

thf('0',plain,(
    ~ ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ( r2_hidden @ X28 @ ( u1_pre_topc @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_pre_topc @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ( r2_hidden @ X28 @ ( u1_pre_topc @ X29 ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_C_1 @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X5 @ X3 @ X6 )
      | ~ ( r2_hidden @ X5 @ ( u1_pre_topc @ X6 ) )
      | ~ ( r2_hidden @ X3 @ ( u1_pre_topc @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['6','14'])).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 @ X7 ) @ ( u1_pre_topc @ X9 ) )
      | ~ ( zip_tseitin_1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ sk_A )
    | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( zip_tseitin_2 @ X17 @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ sk_B_2 @ sk_A )
      | ( zip_tseitin_2 @ X0 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_4,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_12,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v2_pre_topc @ X25 )
      | ( zip_tseitin_3 @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ X0 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( zip_tseitin_1 @ X11 @ X13 @ X12 )
      | ~ ( zip_tseitin_2 @ X11 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A )
      | ( zip_tseitin_1 @ sk_C_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X30: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X30 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( m1_subset_1 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r2_hidden @ X28 @ ( u1_pre_topc @ X29 ) )
      | ( v3_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ sk_A )
    | ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('42',plain,(
    v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gsI6isHddT
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.63  % Solved by: fo/fo7.sh
% 0.43/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.63  % done 476 iterations in 0.173s
% 0.43/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.63  % SZS output start Refutation
% 0.43/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.43/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.43/0.63  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.43/0.63  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.43/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.43/0.63  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.43/0.63  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.43/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.43/0.63  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.43/0.63  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.43/0.63  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.63  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.43/0.63  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.43/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.63  thf(t38_tops_1, conjecture,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63           ( ![C:$i]:
% 0.43/0.63             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63               ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.43/0.63                 ( v3_pre_topc @
% 0.43/0.63                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.63    (~( ![A:$i]:
% 0.43/0.63        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.63          ( ![B:$i]:
% 0.43/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63              ( ![C:$i]:
% 0.43/0.63                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63                  ( ( ( v3_pre_topc @ B @ A ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.43/0.63                    ( v3_pre_topc @
% 0.43/0.63                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.43/0.63    inference('cnf.neg', [status(esa)], [t38_tops_1])).
% 0.43/0.63  thf('0', plain,
% 0.43/0.63      (~ (v3_pre_topc @ 
% 0.43/0.63          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('1', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(d5_pre_topc, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( l1_pre_topc @ A ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63           ( ( v3_pre_topc @ B @ A ) <=>
% 0.43/0.63             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.43/0.63  thf('2', plain,
% 0.43/0.63      (![X28 : $i, X29 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.43/0.63          | ~ (v3_pre_topc @ X28 @ X29)
% 0.43/0.63          | (r2_hidden @ X28 @ (u1_pre_topc @ X29))
% 0.43/0.63          | ~ (l1_pre_topc @ X29))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.63  thf('3', plain,
% 0.43/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.63        | (r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.43/0.63        | ~ (v3_pre_topc @ sk_B_2 @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.43/0.63  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('5', plain, ((v3_pre_topc @ sk_B_2 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('6', plain, ((r2_hidden @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.43/0.63  thf('7', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('8', plain,
% 0.43/0.63      (![X28 : $i, X29 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.43/0.63          | ~ (v3_pre_topc @ X28 @ X29)
% 0.43/0.63          | (r2_hidden @ X28 @ (u1_pre_topc @ X29))
% 0.43/0.63          | ~ (l1_pre_topc @ X29))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.63  thf('9', plain,
% 0.43/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.63        | (r2_hidden @ sk_C_1 @ (u1_pre_topc @ sk_A))
% 0.43/0.63        | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['7', '8'])).
% 0.43/0.63  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('11', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('12', plain, ((r2_hidden @ sk_C_1 @ (u1_pre_topc @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.43/0.63  thf(d1_pre_topc, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( l1_pre_topc @ A ) =>
% 0.43/0.63       ( ( v2_pre_topc @ A ) <=>
% 0.43/0.63         ( ( ![B:$i]:
% 0.43/0.63             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63               ( ![C:$i]:
% 0.43/0.63                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.43/0.63                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.43/0.63                     ( r2_hidden @
% 0.43/0.63                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.43/0.63                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.43/0.63           ( ![B:$i]:
% 0.43/0.63             ( ( m1_subset_1 @
% 0.43/0.63                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.63               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.43/0.63                 ( r2_hidden @
% 0.43/0.63                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.43/0.63                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.43/0.63           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_1, axiom,
% 0.43/0.63    (![C:$i,B:$i,A:$i]:
% 0.43/0.63     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.43/0.63       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.43/0.63         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.43/0.63  thf('13', plain,
% 0.43/0.63      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.43/0.63         ((zip_tseitin_0 @ X5 @ X3 @ X6)
% 0.43/0.63          | ~ (r2_hidden @ X5 @ (u1_pre_topc @ X6))
% 0.43/0.63          | ~ (r2_hidden @ X3 @ (u1_pre_topc @ X6)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.63  thf('14', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 0.43/0.63          | (zip_tseitin_0 @ sk_C_1 @ X0 @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.63  thf('15', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.43/0.63      inference('sup-', [status(thm)], ['6', '14'])).
% 0.43/0.63  thf(zf_stmt_2, axiom,
% 0.43/0.63    (![C:$i,B:$i,A:$i]:
% 0.43/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.43/0.63       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.43/0.63         ( r2_hidden @
% 0.43/0.63           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.43/0.63  thf('16', plain,
% 0.43/0.63      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.43/0.63         (~ (zip_tseitin_0 @ X7 @ X8 @ X9)
% 0.43/0.63          | (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ X9) @ X8 @ X7) @ 
% 0.43/0.63             (u1_pre_topc @ X9))
% 0.43/0.63          | ~ (zip_tseitin_1 @ X7 @ X8 @ X9))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.63  thf('17', plain,
% 0.43/0.63      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ sk_A)
% 0.43/0.63        | (r2_hidden @ 
% 0.43/0.63           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ 
% 0.43/0.63           (u1_pre_topc @ sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.43/0.63  thf('18', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(zf_stmt_3, axiom,
% 0.43/0.63    (![B:$i,A:$i]:
% 0.43/0.63     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.43/0.63       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.43/0.63  thf('19', plain,
% 0.43/0.63      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.43/0.63          | (zip_tseitin_2 @ X17 @ X15 @ X16)
% 0.43/0.63          | ~ (zip_tseitin_3 @ X15 @ X16))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.63  thf('20', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (zip_tseitin_3 @ sk_B_2 @ sk_A)
% 0.43/0.63          | (zip_tseitin_2 @ X0 @ sk_B_2 @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.43/0.63  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf(zf_stmt_4, type, zip_tseitin_5 : $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_5, axiom,
% 0.43/0.63    (![B:$i,A:$i]:
% 0.43/0.63     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.43/0.63       ( ( m1_subset_1 @
% 0.43/0.63           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.63         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.43/0.63  thf(zf_stmt_6, type, zip_tseitin_4 : $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_7, axiom,
% 0.43/0.63    (![B:$i,A:$i]:
% 0.43/0.63     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.43/0.63       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.43/0.63         ( r2_hidden @
% 0.43/0.63           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.43/0.63  thf(zf_stmt_8, type, zip_tseitin_3 : $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_10, axiom,
% 0.43/0.63    (![C:$i,B:$i,A:$i]:
% 0.43/0.63     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.43/0.63       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.63         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.43/0.63  thf(zf_stmt_11, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_12, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.43/0.63  thf(zf_stmt_13, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( l1_pre_topc @ A ) =>
% 0.43/0.63       ( ( v2_pre_topc @ A ) <=>
% 0.43/0.63         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.43/0.63           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.43/0.63           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.43/0.63  thf('22', plain,
% 0.43/0.63      (![X25 : $i, X26 : $i]:
% 0.43/0.63         (~ (v2_pre_topc @ X25)
% 0.43/0.63          | (zip_tseitin_3 @ X26 @ X25)
% 0.43/0.63          | ~ (l1_pre_topc @ X25))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.43/0.63  thf('23', plain,
% 0.43/0.63      (![X0 : $i]: ((zip_tseitin_3 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.43/0.63  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('25', plain, (![X0 : $i]: (zip_tseitin_3 @ X0 @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['23', '24'])).
% 0.43/0.63  thf('26', plain, (![X0 : $i]: (zip_tseitin_2 @ X0 @ sk_B_2 @ sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['20', '25'])).
% 0.43/0.63  thf('27', plain,
% 0.43/0.63      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('28', plain,
% 0.43/0.63      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.43/0.63          | (zip_tseitin_1 @ X11 @ X13 @ X12)
% 0.43/0.63          | ~ (zip_tseitin_2 @ X11 @ X13 @ X12))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.43/0.63  thf('29', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A)
% 0.43/0.63          | (zip_tseitin_1 @ sk_C_1 @ X0 @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.63  thf('30', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_2 @ sk_A)),
% 0.43/0.63      inference('sup-', [status(thm)], ['26', '29'])).
% 0.43/0.63  thf('31', plain,
% 0.43/0.63      ((r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ 
% 0.43/0.63        (u1_pre_topc @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['17', '30'])).
% 0.43/0.63  thf(dt_u1_pre_topc, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( l1_pre_topc @ A ) =>
% 0.43/0.63       ( m1_subset_1 @
% 0.43/0.63         ( u1_pre_topc @ A ) @ 
% 0.43/0.63         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.43/0.63  thf('32', plain,
% 0.43/0.63      (![X30 : $i]:
% 0.43/0.63         ((m1_subset_1 @ (u1_pre_topc @ X30) @ 
% 0.43/0.63           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30))))
% 0.43/0.63          | ~ (l1_pre_topc @ X30))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.43/0.63  thf(t4_subset, axiom,
% 0.43/0.63    (![A:$i,B:$i,C:$i]:
% 0.43/0.63     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.43/0.63       ( m1_subset_1 @ A @ C ) ))).
% 0.43/0.63  thf('33', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.63          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.43/0.63          | (m1_subset_1 @ X0 @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [t4_subset])).
% 0.43/0.63  thf('34', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (~ (l1_pre_topc @ X0)
% 0.43/0.63          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.43/0.63          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.63  thf('35', plain,
% 0.43/0.63      (((m1_subset_1 @ 
% 0.43/0.63         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ 
% 0.43/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['31', '34'])).
% 0.43/0.63  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('37', plain,
% 0.43/0.63      ((m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ 
% 0.43/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('demod', [status(thm)], ['35', '36'])).
% 0.43/0.63  thf('38', plain,
% 0.43/0.63      (![X28 : $i, X29 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.43/0.63          | ~ (r2_hidden @ X28 @ (u1_pre_topc @ X29))
% 0.43/0.63          | (v3_pre_topc @ X28 @ X29)
% 0.43/0.63          | ~ (l1_pre_topc @ X29))),
% 0.43/0.63      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.43/0.63  thf('39', plain,
% 0.43/0.63      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.63        | (v3_pre_topc @ 
% 0.43/0.63           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ sk_A)
% 0.43/0.63        | ~ (r2_hidden @ 
% 0.43/0.63             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ 
% 0.43/0.63             (u1_pre_topc @ sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['37', '38'])).
% 0.43/0.63  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('41', plain,
% 0.43/0.63      ((r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ 
% 0.43/0.63        (u1_pre_topc @ sk_A))),
% 0.43/0.63      inference('demod', [status(thm)], ['17', '30'])).
% 0.43/0.63  thf('42', plain,
% 0.43/0.63      ((v3_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_2 @ sk_C_1) @ 
% 0.43/0.63        sk_A)),
% 0.43/0.63      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.43/0.63  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.43/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

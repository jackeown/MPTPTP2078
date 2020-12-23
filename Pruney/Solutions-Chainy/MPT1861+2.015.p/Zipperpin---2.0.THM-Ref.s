%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KtTCJg4BC7

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:14 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 120 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   15
%              Number of atoms          :  543 (1303 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t29_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tex_2 @ B @ A )
                  | ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v2_tex_2 @ B @ A )
                    | ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( v2_tex_2 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['23','30'])).

thf('32',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( v2_tex_2 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['21'])).

thf('47',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['20','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KtTCJg4BC7
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:01:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 326 iterations in 0.140s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.60  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.60  thf(t29_tex_2, conjecture,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.36/0.60                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i]:
% 0.36/0.60        ( ( l1_pre_topc @ A ) =>
% 0.36/0.60          ( ![B:$i]:
% 0.36/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60              ( ![C:$i]:
% 0.36/0.60                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.36/0.60                    ( v2_tex_2 @
% 0.36/0.60                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.36/0.60  thf('0', plain,
% 0.36/0.60      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k9_subset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.60       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.60         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.36/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.36/0.60           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.60  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.36/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf(t48_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.36/0.60           = (k3_xboole_0 @ X9 @ X10))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t3_subset, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i]:
% 0.36/0.60         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.60  thf('9', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.60  thf(t109_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X18 : $i, X20 : $i]:
% 0.36/0.60         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.60  thf('13', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (m1_subset_1 @ (k4_xboole_0 @ sk_C @ X0) @ 
% 0.36/0.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (m1_subset_1 @ (k3_xboole_0 @ sk_C @ X0) @ 
% 0.36/0.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['6', '13'])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.36/0.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['5', '14'])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(t28_tex_2, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( l1_pre_topc @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.60               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.36/0.60                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.60          | ~ (v2_tex_2 @ X21 @ X22)
% 0.36/0.60          | ~ (r1_tarski @ X23 @ X21)
% 0.36/0.60          | (v2_tex_2 @ X23 @ X22)
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.60          | ~ (l1_pre_topc @ X22))),
% 0.36/0.60      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (l1_pre_topc @ sk_A)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.60          | (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.60          | ~ (r1_tarski @ X0 @ sk_C)
% 0.36/0.60          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.60  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('20', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.60          | (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.60          | ~ (r1_tarski @ X0 @ sk_C)
% 0.36/0.60          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.36/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.60  thf('21', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.36/0.60      inference('split', [status(esa)], ['21'])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.36/0.60           = (k3_xboole_0 @ X9 @ X10))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X18 : $i, X19 : $i]:
% 0.36/0.60         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.60  thf('26', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.60  thf('27', plain,
% 0.36/0.60      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.60         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k4_xboole_0 @ X2 @ X4) @ X3))),
% 0.36/0.60      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.36/0.60  thf('28', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X18 : $i, X20 : $i]:
% 0.36/0.60         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.36/0.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('31', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.36/0.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('sup+', [status(thm)], ['23', '30'])).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('split', [status(esa)], ['21'])).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.60          | ~ (v2_tex_2 @ X21 @ X22)
% 0.36/0.60          | ~ (r1_tarski @ X23 @ X21)
% 0.36/0.60          | (v2_tex_2 @ X23 @ X22)
% 0.36/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.60          | ~ (l1_pre_topc @ X22))),
% 0.36/0.60      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (l1_pre_topc @ sk_A)
% 0.36/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.60          | (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.60          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.60          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.60  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('37', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.60          | (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.60          | ~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.60          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          (~ (r1_tarski @ X0 @ sk_B)
% 0.36/0.60           | (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.60           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.36/0.60         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['32', '37'])).
% 0.36/0.60  thf('39', plain,
% 0.36/0.60      ((![X0 : $i]:
% 0.36/0.60          ((v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.36/0.60           | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)))
% 0.36/0.60         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['31', '38'])).
% 0.36/0.60  thf('40', plain,
% 0.36/0.60      (![X9 : $i, X10 : $i]:
% 0.36/0.60         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 0.36/0.60           = (k3_xboole_0 @ X9 @ X10))),
% 0.36/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.60  thf(t36_xboole_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.60  thf('41', plain,
% 0.36/0.60      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.36/0.60      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.60  thf('42', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.36/0.60         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.36/0.60      inference('demod', [status(thm)], ['39', '42'])).
% 0.36/0.60  thf('44', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.36/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.60  thf('45', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.60  thf('46', plain, (((v2_tex_2 @ sk_C @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.36/0.60      inference('split', [status(esa)], ['21'])).
% 0.36/0.60  thf('47', plain, (((v2_tex_2 @ sk_C @ sk_A))),
% 0.36/0.60      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.36/0.60  thf('48', plain, ((v2_tex_2 @ sk_C @ sk_A)),
% 0.36/0.60      inference('simpl_trail', [status(thm)], ['22', '47'])).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.60          | (v2_tex_2 @ X0 @ sk_A)
% 0.36/0.60          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.36/0.60      inference('demod', [status(thm)], ['20', '48'])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.36/0.60          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.36/0.60      inference('sup-', [status(thm)], ['15', '49'])).
% 0.36/0.60  thf('51', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.60  thf('52', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.36/0.60  thf('53', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.60      inference('sup+', [status(thm)], ['51', '52'])).
% 0.36/0.60  thf('54', plain, (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)),
% 0.36/0.60      inference('demod', [status(thm)], ['50', '53'])).
% 0.36/0.60  thf('55', plain, ($false), inference('demod', [status(thm)], ['4', '54'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

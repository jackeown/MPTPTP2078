%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vBfE9FaXb3

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 142 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  564 (1611 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k3_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('8',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('18',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tex_2 @ X42 @ X43 )
      | ~ ( r1_tarski @ X44 @ X42 )
      | ( v2_tex_2 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('24',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( v2_tex_2 @ X42 @ X43 )
      | ~ ( r1_tarski @ X44 @ X42 )
      | ( v2_tex_2 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A )
        | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_C ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X30 ) @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('33',plain,(
    ! [X29: $i] :
      ( ( k2_subset_1 @ X29 )
      = X29 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('34',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k9_subset_1 @ X36 @ X34 @ X35 )
        = ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['31','42'])).

thf('44',plain,(
    ~ ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('47',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A )
      | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','48'])).

thf('50',plain,(
    v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['6','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vBfE9FaXb3
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:33:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 153 iterations in 0.099s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.39/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.56  thf(t29_tex_2, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.39/0.56                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( l1_pre_topc @ A ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56              ( ![C:$i]:
% 0.39/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.39/0.56                    ( v2_tex_2 @
% 0.39/0.56                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.39/0.56         (((k9_subset_1 @ X36 @ X34 @ X35) = (k3_xboole_0 @ X34 @ X35))
% 0.39/0.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.39/0.56  thf(t12_setfam_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X37 : $i, X38 : $i]:
% 0.39/0.56         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.39/0.56         (((k9_subset_1 @ X36 @ X34 @ X35)
% 0.39/0.56            = (k1_setfam_1 @ (k2_tarski @ X34 @ X35)))
% 0.39/0.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.39/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.39/0.56           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (~ (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.39/0.56      inference('demod', [status(thm)], ['0', '5'])).
% 0.39/0.56  thf(t17_xboole_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (![X37 : $i, X38 : $i]:
% 0.39/0.56         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.39/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ X1)) @ X0)),
% 0.39/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(dt_k9_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (k9_subset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X31))
% 0.39/0.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X31)))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.39/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.39/0.56           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '4'])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ 
% 0.39/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.56  thf('15', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['15'])).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t28_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.39/0.56                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.39/0.56          | ~ (v2_tex_2 @ X42 @ X43)
% 0.39/0.56          | ~ (r1_tarski @ X44 @ X42)
% 0.39/0.56          | (v2_tex_2 @ X44 @ X43)
% 0.39/0.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.39/0.56          | ~ (l1_pre_topc @ X43))),
% 0.39/0.56      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.56  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.56  thf('22', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.56           | (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.56         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['16', '21'])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ 
% 0.39/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['15'])).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.39/0.56          | ~ (v2_tex_2 @ X42 @ X43)
% 0.39/0.56          | ~ (r1_tarski @ X44 @ X42)
% 0.39/0.56          | (v2_tex_2 @ X44 @ X43)
% 0.39/0.56          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.39/0.56          | ~ (l1_pre_topc @ X43))),
% 0.39/0.56      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.56          | ~ (r1_tarski @ X0 @ sk_C)
% 0.39/0.56          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.56  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.56          | ~ (r1_tarski @ X0 @ sk_C)
% 0.39/0.56          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (~ (r1_tarski @ X0 @ sk_C)
% 0.39/0.56           | (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.56           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.39/0.56         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['24', '29'])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          ((v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A)
% 0.39/0.56           | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_C)))
% 0.39/0.56         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['23', '30'])).
% 0.39/0.56  thf(dt_k2_subset_1, axiom,
% 0.39/0.56    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      (![X30 : $i]: (m1_subset_1 @ (k2_subset_1 @ X30) @ (k1_zfmisc_1 @ X30))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.39/0.56  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.39/0.56  thf('33', plain, (![X29 : $i]: ((k2_subset_1 @ X29) = (X29))),
% 0.39/0.56      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.39/0.56  thf('34', plain, (![X30 : $i]: (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X30))),
% 0.39/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (k9_subset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X31))
% 0.39/0.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X31)))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.56  thf(t3_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (![X39 : $i, X40 : $i]:
% 0.39/0.56         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.39/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.56  thf('39', plain, (![X30 : $i]: (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X30))),
% 0.39/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.39/0.56  thf('40', plain,
% 0.39/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.39/0.56         (((k9_subset_1 @ X36 @ X34 @ X35)
% 0.39/0.56            = (k1_setfam_1 @ (k2_tarski @ X34 @ X35)))
% 0.39/0.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.39/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         ((k9_subset_1 @ X0 @ X1 @ X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.39/0.56      inference('demod', [status(thm)], ['38', '41'])).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      ((![X0 : $i]: (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A))
% 0.39/0.56         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['31', '42'])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (~ (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.39/0.56      inference('demod', [status(thm)], ['0', '5'])).
% 0.39/0.56  thf('45', plain, (~ ((v2_tex_2 @ sk_C @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('46', plain, (((v2_tex_2 @ sk_B @ sk_A)) | ((v2_tex_2 @ sk_C @ sk_A))),
% 0.39/0.56      inference('split', [status(esa)], ['15'])).
% 0.39/0.56  thf('47', plain, (((v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.39/0.56  thf('48', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.56          | (v2_tex_2 @ X0 @ sk_A)
% 0.39/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('simpl_trail', [status(thm)], ['22', '47'])).
% 0.39/0.56  thf('49', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A)
% 0.39/0.56          | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_B))),
% 0.39/0.56      inference('sup-', [status(thm)], ['14', '48'])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      ((v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '49'])).
% 0.39/0.56  thf('51', plain, ($false), inference('demod', [status(thm)], ['6', '50'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

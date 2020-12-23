%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6RxBS1LFaW

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 127 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  542 (1339 expanded)
%              Number of equality atoms :   10 (  22 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ( v2_tex_2 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ( v2_tex_2 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('47',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('49',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['26','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['4','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6RxBS1LFaW
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 116 iterations in 0.114s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.56  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.56  thf(t29_tex_2, conjecture,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( l1_pre_topc @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56           ( ![C:$i]:
% 0.37/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.56                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i]:
% 0.37/0.56        ( ( l1_pre_topc @ A ) =>
% 0.37/0.56          ( ![B:$i]:
% 0.37/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56              ( ![C:$i]:
% 0.37/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.56                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.56                    ( v2_tex_2 @
% 0.37/0.56                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.37/0.56  thf('2', plain,
% 0.37/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.37/0.56         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.37/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.37/0.56           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.37/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.56  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.37/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(t3_subset, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]:
% 0.37/0.56         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.37/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.56  thf('7', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf(commutativity_k2_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.37/0.56  thf(t12_setfam_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.56  thf('9', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.56  thf('10', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         ((k1_setfam_1 @ (k2_tarski @ X10 @ X11)) = (k3_xboole_0 @ X10 @ X11))),
% 0.37/0.56      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf(t17_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.37/0.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.56      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.56  thf(t1_xboole_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.37/0.56       ( r1_tarski @ A @ C ) ))).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.56         (~ (r1_tarski @ X2 @ X3)
% 0.37/0.56          | ~ (r1_tarski @ X3 @ X4)
% 0.37/0.56          | (r1_tarski @ X2 @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['7', '16'])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X12 : $i, X14 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.37/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(t28_tex_2, axiom,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( l1_pre_topc @ A ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.57               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.37/0.57                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.57          | ~ (v2_tex_2 @ X15 @ X16)
% 0.37/0.57          | ~ (r1_tarski @ X17 @ X15)
% 0.37/0.57          | (v2_tex_2 @ X17 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.57          | ~ (l1_pre_topc @ X16))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.37/0.57  thf('22', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C)
% 0.37/0.57          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C)
% 0.37/0.57          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('26', plain,
% 0.37/0.57      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['25'])).
% 0.37/0.57  thf('27', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('28', plain,
% 0.37/0.57      (![X12 : $i, X13 : $i]:
% 0.37/0.57         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.57  thf('29', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.57  thf('30', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.57         (~ (r1_tarski @ X2 @ X3)
% 0.37/0.57          | ~ (r1_tarski @ X3 @ X4)
% 0.37/0.57          | (r1_tarski @ X2 @ X4))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.57         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['29', '32'])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X12 : $i, X14 : $i]:
% 0.37/0.57         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.37/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf('36', plain,
% 0.37/0.57      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('split', [status(esa)], ['25'])).
% 0.37/0.57  thf('37', plain,
% 0.37/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('38', plain,
% 0.37/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.57          | ~ (v2_tex_2 @ X15 @ X16)
% 0.37/0.57          | ~ (r1_tarski @ X17 @ X15)
% 0.37/0.57          | (v2_tex_2 @ X17 @ X16)
% 0.37/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.37/0.57          | ~ (l1_pre_topc @ X16))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (l1_pre_topc @ sk_A)
% 0.37/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.57  thf('42', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          (~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.57           | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.57         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['36', '41'])).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      ((![X0 : $i]:
% 0.37/0.57          ((v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.37/0.57           | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)))
% 0.37/0.57         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['35', '42'])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.37/0.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.37/0.57         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.37/0.57  thf('46', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.37/0.57  thf('47', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('48', plain, (((v2_tex_2 @ sk_C @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.57      inference('split', [status(esa)], ['25'])).
% 0.37/0.57  thf('49', plain, (((v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.57      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.37/0.57  thf('50', plain, ((v2_tex_2 @ sk_C @ sk_A)),
% 0.37/0.57      inference('simpl_trail', [status(thm)], ['26', '49'])).
% 0.37/0.57  thf('51', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.57          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.37/0.57      inference('demod', [status(thm)], ['24', '50'])).
% 0.37/0.57  thf('52', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.37/0.57          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['19', '51'])).
% 0.37/0.57  thf('53', plain,
% 0.37/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.37/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.37/0.57  thf('54', plain, (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)),
% 0.37/0.57      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.57  thf('55', plain, ($false), inference('demod', [status(thm)], ['4', '54'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

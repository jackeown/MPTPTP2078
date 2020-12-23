%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.odLE91zMse

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:12 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 176 expanded)
%              Number of leaves         :   23 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  613 (1749 expanded)
%              Number of equality atoms :   13 (  46 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_tarski @ X15 @ X14 )
      = ( k2_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_A )
   <= ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ( v2_tex_2 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C_1 )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('38',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ( v2_tex_2 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['36','49'])).

thf('51',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('52',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('54',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['35','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','55'])).

thf('57',plain,(
    v2_tex_2 @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['5','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('59',plain,(
    v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['4','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.odLE91zMse
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:57:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 748 iterations in 0.518s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.96  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.96  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/0.96  thf(t29_tex_2, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.76/0.96                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( l1_pre_topc @ A ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96              ( ![C:$i]:
% 0.76/0.96                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.76/0.96                    ( v2_tex_2 @
% 0.76/0.96                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1) @ 
% 0.76/0.96          sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k9_subset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.96       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.96         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 0.76/0.96          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.76/0.96           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.76/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.76/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.96  thf(t17_xboole_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.76/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.96  thf(d3_tarski, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (![X1 : $i, X3 : $i]:
% 0.76/0.96         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf(commutativity_k2_tarski, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (![X14 : $i, X15 : $i]:
% 0.76/0.96         ((k2_tarski @ X15 @ X14) = (k2_tarski @ X14 @ X15))),
% 0.76/0.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.76/0.96  thf(t12_setfam_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.76/0.96  thf('8', plain,
% 0.76/0.96      (![X19 : $i, X20 : $i]:
% 0.76/0.96         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['7', '8'])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      (![X19 : $i, X20 : $i]:
% 0.76/0.96         ((k1_setfam_1 @ (k2_tarski @ X19 @ X20)) = (k3_xboole_0 @ X19 @ X20))),
% 0.76/0.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.76/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X0 @ X1)
% 0.76/0.96          | (r2_hidden @ X0 @ X2)
% 0.76/0.96          | ~ (r1_tarski @ X1 @ X2))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['11', '14'])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.76/0.96          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['6', '15'])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t3_subset, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      (![X21 : $i, X22 : $i]:
% 0.76/0.96         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('19', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X0 @ X1)
% 0.76/0.96          | (r2_hidden @ X0 @ X2)
% 0.76/0.96          | ~ (r1_tarski @ X1 @ X2))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]:
% 0.76/0.96         ((r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ X1)
% 0.76/0.96          | (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ X0 @ sk_B)) @ 
% 0.76/0.96             (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['16', '21'])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      (![X1 : $i, X3 : $i]:
% 0.76/0.96         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.76/0.96          | (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('simplify', [status(thm)], ['24'])).
% 0.76/0.96  thf('26', plain,
% 0.76/0.96      (![X21 : $i, X23 : $i]:
% 0.76/0.96         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('27', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.96  thf('28', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (((v2_tex_2 @ sk_C_1 @ sk_A)) <= (((v2_tex_2 @ sk_C_1 @ sk_A)))),
% 0.76/0.96      inference('split', [status(esa)], ['28'])).
% 0.76/0.96  thf('30', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t28_tex_2, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.76/0.96                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.76/0.96  thf('31', plain,
% 0.76/0.96      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.76/0.96          | ~ (v2_tex_2 @ X24 @ X25)
% 0.76/0.96          | ~ (r1_tarski @ X26 @ X24)
% 0.76/0.96          | (v2_tex_2 @ X26 @ X25)
% 0.76/0.96          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.76/0.96          | ~ (l1_pre_topc @ X25))),
% 0.76/0.96      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | (v2_tex_2 @ X0 @ sk_A)
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.76/0.96          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['30', '31'])).
% 0.76/0.96  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | (v2_tex_2 @ X0 @ sk_A)
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.76/0.96          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['32', '33'])).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      ((![X0 : $i]:
% 0.76/0.96          (~ (r1_tarski @ X0 @ sk_C_1)
% 0.76/0.96           | (v2_tex_2 @ X0 @ sk_A)
% 0.76/0.96           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.76/0.96         <= (((v2_tex_2 @ sk_C_1 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['29', '34'])).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.76/0.96          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.96  thf('38', plain,
% 0.76/0.96      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('split', [status(esa)], ['28'])).
% 0.76/0.96  thf('39', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.76/0.96          | ~ (v2_tex_2 @ X24 @ X25)
% 0.76/0.96          | ~ (r1_tarski @ X26 @ X24)
% 0.76/0.96          | (v2_tex_2 @ X26 @ X25)
% 0.76/0.96          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.76/0.96          | ~ (l1_pre_topc @ X25))),
% 0.76/0.96      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | (v2_tex_2 @ X0 @ sk_A)
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.96  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | (v2_tex_2 @ X0 @ sk_A)
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf('44', plain,
% 0.76/0.96      ((![X0 : $i]:
% 0.76/0.96          (~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96           | (v2_tex_2 @ X0 @ sk_A)
% 0.76/0.96           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.76/0.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['38', '43'])).
% 0.76/0.96  thf('45', plain,
% 0.76/0.96      ((![X0 : $i]:
% 0.76/0.96          ((v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.76/0.96           | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)))
% 0.76/0.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['37', '44'])).
% 0.76/0.96  thf('46', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('47', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 0.76/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.76/0.96  thf('48', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.76/0.96      inference('sup+', [status(thm)], ['46', '47'])).
% 0.76/0.96  thf('49', plain,
% 0.76/0.96      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))
% 0.76/0.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['45', '48'])).
% 0.76/0.96  thf('50', plain,
% 0.76/0.96      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.76/0.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['36', '49'])).
% 0.76/0.96  thf('51', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.76/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.96  thf('52', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/0.96  thf('53', plain, (((v2_tex_2 @ sk_C_1 @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.76/0.96      inference('split', [status(esa)], ['28'])).
% 0.76/0.96  thf('54', plain, (((v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.76/0.96      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.76/0.96  thf('55', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (r1_tarski @ X0 @ sk_C_1)
% 0.76/0.96          | (v2_tex_2 @ X0 @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.96      inference('simpl_trail', [status(thm)], ['35', '54'])).
% 0.76/0.96  thf('56', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.76/0.96          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_C_1))),
% 0.76/0.96      inference('sup-', [status(thm)], ['27', '55'])).
% 0.76/0.96  thf('57', plain, ((v2_tex_2 @ (k3_xboole_0 @ sk_C_1 @ sk_B) @ sk_A)),
% 0.76/0.96      inference('sup-', [status(thm)], ['5', '56'])).
% 0.76/0.96  thf('58', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.76/0.96      inference('sup+', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('59', plain, ((v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.76/0.96      inference('demod', [status(thm)], ['57', '58'])).
% 0.76/0.96  thf('60', plain, ($false), inference('demod', [status(thm)], ['4', '59'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

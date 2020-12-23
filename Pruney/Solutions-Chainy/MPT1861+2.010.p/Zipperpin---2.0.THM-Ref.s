%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KKhVfhp1Tj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 150 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   15
%              Number of atoms          :  634 (1563 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k1_setfam_1 @ ( k2_tarski @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X37: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_C @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ( v2_tex_2 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X37: $i,X39: $i] :
      ( ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( r1_tarski @ X37 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf('39',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v2_tex_2 @ X43 @ X44 )
      | ~ ( r1_tarski @ X45 @ X43 )
      | ( v2_tex_2 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A )
        | ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X12 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    ~ ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('52',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['28'])).

thf('54',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['29','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_C )
      | ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['6','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KKhVfhp1Tj
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:41:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 237 iterations in 0.124s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.58  thf(t29_tex_2, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.58                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( l1_pre_topc @ A ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58              ( ![C:$i]:
% 0.37/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.37/0.58                    ( v2_tex_2 @
% 0.37/0.58                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(redefinition_k9_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.58         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 0.37/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.37/0.58      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.37/0.58  thf(t12_setfam_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X35 : $i, X36 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.37/0.58         (((k9_subset_1 @ X27 @ X25 @ X26)
% 0.37/0.58            = (k1_setfam_1 @ (k2_tarski @ X25 @ X26)))
% 0.37/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.37/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.37/0.58           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '4'])).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (~ (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '5'])).
% 0.37/0.58  thf(commutativity_k3_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X35 : $i, X36 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X35 : $i, X36 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.37/0.58           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.37/0.58  thf(t48_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X12 : $i, X13 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.58           = (k3_xboole_0 @ X12 @ X13))),
% 0.37/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (![X35 : $i, X36 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.37/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.37/0.58  thf('13', plain,
% 0.37/0.58      (![X12 : $i, X13 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.58           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 0.37/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t3_subset, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X37 : $i, X38 : $i]:
% 0.37/0.58         ((r1_tarski @ X37 @ X38) | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('16', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.58  thf(t109_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.58         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X37 : $i, X39 : $i]:
% 0.37/0.58         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X37 @ X39))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('20', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k4_xboole_0 @ sk_C @ X0) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ sk_C @ X0)) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['13', '20'])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['10', '21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t28_tex_2, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.37/0.58                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.58          | ~ (v2_tex_2 @ X43 @ X44)
% 0.37/0.58          | ~ (r1_tarski @ X45 @ X43)
% 0.37/0.58          | (v2_tex_2 @ X45 @ X44)
% 0.37/0.58          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.58          | ~ (l1_pre_topc @ X44))),
% 0.37/0.58      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ sk_A)
% 0.37/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.58          | ~ (r1_tarski @ X0 @ sk_C)
% 0.37/0.58          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.58  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('27', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.58          | ~ (r1_tarski @ X0 @ sk_C)
% 0.37/0.58          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.58  thf('28', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['28'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (![X12 : $i, X13 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.58           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 0.37/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X37 : $i, X38 : $i]:
% 0.37/0.58         ((r1_tarski @ X37 @ X38) | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('33', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.37/0.58         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (![X37 : $i, X39 : $i]:
% 0.37/0.58         ((m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X39)) | ~ (r1_tarski @ X37 @ X39))),
% 0.37/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ 
% 0.37/0.58          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['30', '37'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['28'])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.58          | ~ (v2_tex_2 @ X43 @ X44)
% 0.37/0.58          | ~ (r1_tarski @ X45 @ X43)
% 0.37/0.58          | (v2_tex_2 @ X45 @ X44)
% 0.37/0.58          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.37/0.58          | ~ (l1_pre_topc @ X44))),
% 0.37/0.58      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ sk_A)
% 0.37/0.58          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.58          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.58          | ~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.58          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      ((![X0 : $i]:
% 0.37/0.58          (~ (r1_tarski @ X0 @ sk_B)
% 0.37/0.58           | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.58           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.37/0.58         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['39', '44'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      ((![X0 : $i]:
% 0.37/0.58          ((v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A)
% 0.37/0.58           | ~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_B)))
% 0.37/0.58         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['38', '45'])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (![X12 : $i, X13 : $i]:
% 0.37/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.58           = (k1_setfam_1 @ (k2_tarski @ X12 @ X13)))),
% 0.37/0.58      inference('demod', [status(thm)], ['11', '12'])).
% 0.37/0.58  thf(t36_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 0.37/0.58      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 0.37/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      ((![X0 : $i]: (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)) @ sk_A))
% 0.37/0.58         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['46', '49'])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      (~ (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C)) @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['0', '5'])).
% 0.37/0.58  thf('52', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('53', plain, (((v2_tex_2 @ sk_C @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.37/0.58      inference('split', [status(esa)], ['28'])).
% 0.37/0.58  thf('54', plain, (((v2_tex_2 @ sk_C @ sk_A))),
% 0.37/0.58      inference('sat_resolution*', [status(thm)], ['52', '53'])).
% 0.37/0.58  thf('55', plain, ((v2_tex_2 @ sk_C @ sk_A)),
% 0.37/0.58      inference('simpl_trail', [status(thm)], ['29', '54'])).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58          | (v2_tex_2 @ X0 @ sk_A)
% 0.37/0.58          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.37/0.58      inference('demod', [status(thm)], ['27', '55'])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_C)
% 0.37/0.58          | (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['22', '56'])).
% 0.37/0.58  thf('58', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.37/0.58           = (k1_setfam_1 @ (k2_tarski @ X0 @ X1)))),
% 0.37/0.58      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X1)),
% 0.37/0.58      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.58  thf('60', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 0.37/0.58      inference('sup+', [status(thm)], ['58', '59'])).
% 0.37/0.58  thf('61', plain,
% 0.37/0.58      (![X0 : $i]: (v2_tex_2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)) @ sk_A)),
% 0.37/0.58      inference('demod', [status(thm)], ['57', '60'])).
% 0.37/0.58  thf('62', plain, ($false), inference('demod', [status(thm)], ['6', '61'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

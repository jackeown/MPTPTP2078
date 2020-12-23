%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gIfyVfza4b

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:36 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 122 expanded)
%              Number of leaves         :   37 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  568 ( 869 expanded)
%              Number of equality atoms :   37 (  43 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X27 @ X28 ) @ X27 )
      | ( v2_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('25',plain,(
    ! [X26: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X16 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('28',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('29',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X28 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ X30 )
       != ( sk_C_1 @ X27 @ X28 ) )
      | ( v2_tex_2 @ X27 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X12 @ X14 @ X13 )
        = ( k9_subset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k9_subset_1 @ X19 @ X17 @ X18 )
        = ( k3_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('52',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49','50','53'])).

thf('55',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['4','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gIfyVfza4b
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:38:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.92/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.11  % Solved by: fo/fo7.sh
% 0.92/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.11  % done 1672 iterations in 0.654s
% 0.92/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.11  % SZS output start Refutation
% 0.92/1.11  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.92/1.11  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.92/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.92/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.11  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.92/1.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.92/1.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.92/1.11  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.92/1.11  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.92/1.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.92/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.11  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.92/1.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.92/1.11  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.92/1.11  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.92/1.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.92/1.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.92/1.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.92/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.11  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.92/1.11  thf(t35_tex_2, conjecture,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.92/1.11       ( ![B:$i]:
% 0.92/1.11         ( ( ( v1_xboole_0 @ B ) & 
% 0.92/1.11             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.92/1.11           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.92/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.11    (~( ![A:$i]:
% 0.92/1.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.92/1.11            ( l1_pre_topc @ A ) ) =>
% 0.92/1.11          ( ![B:$i]:
% 0.92/1.11            ( ( ( v1_xboole_0 @ B ) & 
% 0.92/1.11                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.92/1.11              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.92/1.11    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.92/1.11  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(l13_xboole_0, axiom,
% 0.92/1.11    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.92/1.11  thf('2', plain,
% 0.92/1.11      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['1', '2'])).
% 0.92/1.11  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.92/1.11      inference('demod', [status(thm)], ['0', '3'])).
% 0.92/1.11  thf('5', plain,
% 0.92/1.11      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf(t4_subset_1, axiom,
% 0.92/1.11    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.92/1.11  thf('6', plain,
% 0.92/1.11      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.92/1.11      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.92/1.11  thf(d5_tex_2, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( l1_pre_topc @ A ) =>
% 0.92/1.11       ( ![B:$i]:
% 0.92/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.11           ( ( v2_tex_2 @ B @ A ) <=>
% 0.92/1.11             ( ![C:$i]:
% 0.92/1.11               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.11                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.92/1.11                      ( ![D:$i]:
% 0.92/1.11                        ( ( m1_subset_1 @
% 0.92/1.11                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.92/1.11                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.92/1.11                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.92/1.11                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.92/1.11  thf('7', plain,
% 0.92/1.11      (![X27 : $i, X28 : $i]:
% 0.92/1.11         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.92/1.11          | (r1_tarski @ (sk_C_1 @ X27 @ X28) @ X27)
% 0.92/1.11          | (v2_tex_2 @ X27 @ X28)
% 0.92/1.11          | ~ (l1_pre_topc @ X28))),
% 0.92/1.11      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.92/1.11  thf('8', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (l1_pre_topc @ X0)
% 0.92/1.11          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['6', '7'])).
% 0.92/1.11  thf(d3_tarski, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( r1_tarski @ A @ B ) <=>
% 0.92/1.11       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.92/1.11  thf('9', plain,
% 0.92/1.11      (![X4 : $i, X6 : $i]:
% 0.92/1.11         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.92/1.11      inference('cnf', [status(esa)], [d3_tarski])).
% 0.92/1.11  thf(d1_xboole_0, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.92/1.11  thf('10', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.92/1.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.92/1.11  thf('11', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['9', '10'])).
% 0.92/1.11  thf(d10_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.92/1.11  thf('12', plain,
% 0.92/1.11      (![X8 : $i, X10 : $i]:
% 0.92/1.11         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.92/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.11  thf('13', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['11', '12'])).
% 0.92/1.11  thf('14', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ~ (l1_pre_topc @ X0)
% 0.92/1.11          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.92/1.11          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['8', '13'])).
% 0.92/1.11  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.92/1.11  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.11  thf('16', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ~ (l1_pre_topc @ X0)
% 0.92/1.11          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.92/1.11      inference('demod', [status(thm)], ['14', '15'])).
% 0.92/1.11  thf('17', plain,
% 0.92/1.11      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.92/1.11      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.92/1.11  thf('18', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.92/1.11      inference('demod', [status(thm)], ['0', '3'])).
% 0.92/1.11  thf('19', plain,
% 0.92/1.11      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.92/1.11  thf('20', plain,
% 0.92/1.11      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.92/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.92/1.11        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['16', '19'])).
% 0.92/1.11  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.11  thf('23', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.92/1.11  thf('24', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (((sk_C_1 @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.92/1.11      inference('sup+', [status(thm)], ['5', '23'])).
% 0.92/1.11  thf(fc10_tops_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.92/1.11       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.92/1.11  thf('25', plain,
% 0.92/1.11      (![X26 : $i]:
% 0.92/1.11         ((v3_pre_topc @ (k2_struct_0 @ X26) @ X26)
% 0.92/1.11          | ~ (l1_pre_topc @ X26)
% 0.92/1.11          | ~ (v2_pre_topc @ X26))),
% 0.92/1.11      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.92/1.11  thf(d3_struct_0, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.92/1.11  thf('26', plain,
% 0.92/1.11      (![X24 : $i]:
% 0.92/1.11         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.92/1.11      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.92/1.11  thf(dt_k2_subset_1, axiom,
% 0.92/1.11    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.92/1.11  thf('27', plain,
% 0.92/1.11      (![X16 : $i]: (m1_subset_1 @ (k2_subset_1 @ X16) @ (k1_zfmisc_1 @ X16))),
% 0.92/1.11      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.92/1.11  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.92/1.11  thf('28', plain, (![X15 : $i]: ((k2_subset_1 @ X15) = (X15))),
% 0.92/1.11      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.92/1.11  thf('29', plain, (![X16 : $i]: (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X16))),
% 0.92/1.11      inference('demod', [status(thm)], ['27', '28'])).
% 0.92/1.11  thf('30', plain,
% 0.92/1.11      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.92/1.11      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.92/1.11  thf('31', plain,
% 0.92/1.11      (![X27 : $i, X28 : $i, X30 : $i]:
% 0.92/1.11         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.92/1.11          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.92/1.11          | ~ (v3_pre_topc @ X30 @ X28)
% 0.92/1.11          | ((k9_subset_1 @ (u1_struct_0 @ X28) @ X27 @ X30)
% 0.92/1.11              != (sk_C_1 @ X27 @ X28))
% 0.92/1.11          | (v2_tex_2 @ X27 @ X28)
% 0.92/1.11          | ~ (l1_pre_topc @ X28))),
% 0.92/1.11      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.92/1.11  thf('32', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (l1_pre_topc @ X0)
% 0.92/1.11          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.92/1.11              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.92/1.11          | ~ (v3_pre_topc @ X1 @ X0)
% 0.92/1.11          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['30', '31'])).
% 0.92/1.11  thf('33', plain,
% 0.92/1.11      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.92/1.11      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.92/1.11  thf(commutativity_k9_subset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.92/1.11       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.92/1.11  thf('34', plain,
% 0.92/1.11      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.92/1.11         (((k9_subset_1 @ X12 @ X14 @ X13) = (k9_subset_1 @ X12 @ X13 @ X14))
% 0.92/1.11          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.92/1.11      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.92/1.11  thf('35', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.92/1.11           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.92/1.11      inference('sup-', [status(thm)], ['33', '34'])).
% 0.92/1.11  thf('36', plain,
% 0.92/1.11      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 0.92/1.11      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.92/1.11  thf(redefinition_k9_subset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.92/1.11       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.92/1.11  thf('37', plain,
% 0.92/1.11      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.92/1.11         (((k9_subset_1 @ X19 @ X17 @ X18) = (k3_xboole_0 @ X17 @ X18))
% 0.92/1.11          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.92/1.11      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.92/1.11  thf('38', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.92/1.11           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['36', '37'])).
% 0.92/1.11  thf(t2_boole, axiom,
% 0.92/1.11    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.92/1.11  thf('39', plain,
% 0.92/1.11      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('cnf', [status(esa)], [t2_boole])).
% 0.92/1.11  thf('40', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.92/1.11      inference('demod', [status(thm)], ['38', '39'])).
% 0.92/1.11  thf('41', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.92/1.11      inference('demod', [status(thm)], ['35', '40'])).
% 0.92/1.11  thf('42', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (l1_pre_topc @ X0)
% 0.92/1.11          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.92/1.11          | ~ (v3_pre_topc @ X1 @ X0)
% 0.92/1.11          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.92/1.11      inference('demod', [status(thm)], ['32', '41'])).
% 0.92/1.11  thf('43', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.92/1.11          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.92/1.11          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ~ (l1_pre_topc @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['29', '42'])).
% 0.92/1.11  thf('44', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.92/1.11          | ~ (l1_struct_0 @ X0)
% 0.92/1.11          | ~ (l1_pre_topc @ X0)
% 0.92/1.11          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['26', '43'])).
% 0.92/1.11  thf('45', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (v2_pre_topc @ X0)
% 0.92/1.11          | ~ (l1_pre_topc @ X0)
% 0.92/1.11          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.92/1.11          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ~ (l1_pre_topc @ X0)
% 0.92/1.11          | ~ (l1_struct_0 @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['25', '44'])).
% 0.92/1.11  thf('46', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         (~ (l1_struct_0 @ X0)
% 0.92/1.11          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.92/1.11          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.92/1.11          | ~ (l1_pre_topc @ X0)
% 0.92/1.11          | ~ (v2_pre_topc @ X0))),
% 0.92/1.11      inference('simplify', [status(thm)], ['45'])).
% 0.92/1.11  thf('47', plain,
% 0.92/1.11      ((((k1_xboole_0) != (k1_xboole_0))
% 0.92/1.11        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.92/1.11        | ~ (v2_pre_topc @ sk_A)
% 0.92/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.92/1.11        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.92/1.11        | ~ (l1_struct_0 @ sk_A))),
% 0.92/1.11      inference('sup-', [status(thm)], ['24', '46'])).
% 0.92/1.11  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.92/1.11      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.92/1.11  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(dt_l1_pre_topc, axiom,
% 0.92/1.11    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.92/1.11  thf('52', plain,
% 0.92/1.11      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.92/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.92/1.11  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 0.92/1.11      inference('sup-', [status(thm)], ['51', '52'])).
% 0.92/1.11  thf('54', plain,
% 0.92/1.11      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['47', '48', '49', '50', '53'])).
% 0.92/1.11  thf('55', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.92/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.92/1.11  thf('56', plain, ($false), inference('demod', [status(thm)], ['4', '55'])).
% 0.92/1.11  
% 0.92/1.11  % SZS output end Refutation
% 0.92/1.11  
% 0.92/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

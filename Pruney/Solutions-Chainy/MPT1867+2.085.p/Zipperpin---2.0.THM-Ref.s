%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AM7PjEC6n4

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:37 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 133 expanded)
%              Number of leaves         :   31 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  574 ( 942 expanded)
%              Number of equality atoms :   30 (  39 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('32',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
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

thf('33',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X26 )
       != ( sk_C_1 @ X23 @ X24 ) )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X23 @ X24 ) @ X23 )
      | ( v2_tex_2 @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('53',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','44','58'])).

thf('60',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['4','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AM7PjEC6n4
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.85/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.85/1.04  % Solved by: fo/fo7.sh
% 0.85/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.04  % done 532 iterations in 0.566s
% 0.85/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.85/1.04  % SZS output start Refutation
% 0.85/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.04  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.85/1.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.85/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.04  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.85/1.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.85/1.04  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.85/1.04  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.85/1.04  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.85/1.04  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.85/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.04  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.85/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.85/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.85/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.04  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.85/1.04  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.85/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.85/1.04  thf(t35_tex_2, conjecture,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.85/1.04       ( ![B:$i]:
% 0.85/1.04         ( ( ( v1_xboole_0 @ B ) & 
% 0.85/1.04             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.85/1.04           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.85/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.04    (~( ![A:$i]:
% 0.85/1.04        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.85/1.04            ( l1_pre_topc @ A ) ) =>
% 0.85/1.04          ( ![B:$i]:
% 0.85/1.04            ( ( ( v1_xboole_0 @ B ) & 
% 0.85/1.04                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.85/1.04              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.85/1.04    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.85/1.04  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf(l13_xboole_0, axiom,
% 0.85/1.04    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.85/1.04  thf('2', plain,
% 0.85/1.04      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.85/1.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.04  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['1', '2'])).
% 0.85/1.04  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.85/1.04      inference('demod', [status(thm)], ['0', '3'])).
% 0.85/1.04  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('6', plain,
% 0.85/1.04      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.85/1.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.04  thf('7', plain,
% 0.85/1.04      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.85/1.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.04  thf(t4_subset_1, axiom,
% 0.85/1.04    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.85/1.04  thf('8', plain,
% 0.85/1.04      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.85/1.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.85/1.04  thf(t44_tops_1, axiom,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( l1_pre_topc @ A ) =>
% 0.85/1.04       ( ![B:$i]:
% 0.85/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.04           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.85/1.04  thf('9', plain,
% 0.85/1.04      (![X21 : $i, X22 : $i]:
% 0.85/1.04         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.85/1.04          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 0.85/1.04          | ~ (l1_pre_topc @ X22))),
% 0.85/1.04      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.85/1.04  thf('10', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (l1_pre_topc @ X0)
% 0.85/1.04          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['8', '9'])).
% 0.85/1.04  thf(d3_tarski, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( r1_tarski @ A @ B ) <=>
% 0.85/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.85/1.04  thf('11', plain,
% 0.85/1.04      (![X4 : $i, X6 : $i]:
% 0.85/1.04         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.04  thf(d1_xboole_0, axiom,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.85/1.04  thf('12', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.85/1.04      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.85/1.04  thf('13', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['11', '12'])).
% 0.85/1.04  thf(d10_xboole_0, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.04  thf('14', plain,
% 0.85/1.04      (![X8 : $i, X10 : $i]:
% 0.85/1.04         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.85/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.04  thf('15', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.04  thf('16', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (l1_pre_topc @ X0)
% 0.85/1.04          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['10', '15'])).
% 0.85/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.85/1.04  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.04  thf('18', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (l1_pre_topc @ X0)
% 0.85/1.04          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['16', '17'])).
% 0.85/1.04  thf('19', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         (((k1_tops_1 @ X1 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X1))),
% 0.85/1.04      inference('sup+', [status(thm)], ['7', '18'])).
% 0.85/1.04  thf('20', plain,
% 0.85/1.04      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.85/1.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.85/1.04  thf(fc9_tops_1, axiom,
% 0.85/1.04    (![A:$i,B:$i]:
% 0.85/1.04     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.85/1.04         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.85/1.04       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.85/1.04  thf('21', plain,
% 0.85/1.04      (![X19 : $i, X20 : $i]:
% 0.85/1.04         (~ (l1_pre_topc @ X19)
% 0.85/1.04          | ~ (v2_pre_topc @ X19)
% 0.85/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.85/1.04          | (v3_pre_topc @ (k1_tops_1 @ X19 @ X20) @ X19))),
% 0.85/1.04      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.85/1.04  thf('22', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((v3_pre_topc @ (k1_tops_1 @ X0 @ k1_xboole_0) @ X0)
% 0.85/1.04          | ~ (v2_pre_topc @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['20', '21'])).
% 0.85/1.04  thf('23', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0)
% 0.85/1.04          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0)
% 0.85/1.04          | ~ (v2_pre_topc @ X0))),
% 0.85/1.04      inference('sup+', [status(thm)], ['19', '22'])).
% 0.85/1.04  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.04  thf('25', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0)
% 0.85/1.04          | ~ (v2_pre_topc @ X0))),
% 0.85/1.04      inference('demod', [status(thm)], ['23', '24'])).
% 0.85/1.04  thf('26', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (v2_pre_topc @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0)
% 0.85/1.04          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['25'])).
% 0.85/1.04  thf('27', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((v3_pre_topc @ X0 @ X1)
% 0.85/1.04          | ~ (v1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X1)
% 0.85/1.04          | ~ (v2_pre_topc @ X1))),
% 0.85/1.04      inference('sup+', [status(thm)], ['6', '26'])).
% 0.85/1.04  thf('28', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (v2_pre_topc @ sk_A)
% 0.85/1.04          | ~ (v1_xboole_0 @ X0)
% 0.85/1.04          | (v3_pre_topc @ X0 @ sk_A))),
% 0.85/1.04      inference('sup-', [status(thm)], ['5', '27'])).
% 0.85/1.04  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('30', plain,
% 0.85/1.04      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.85/1.04      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.04  thf('31', plain,
% 0.85/1.04      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.85/1.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.85/1.04  thf('32', plain,
% 0.85/1.04      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.85/1.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.85/1.04  thf(d5_tex_2, axiom,
% 0.85/1.04    (![A:$i]:
% 0.85/1.04     ( ( l1_pre_topc @ A ) =>
% 0.85/1.04       ( ![B:$i]:
% 0.85/1.04         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.04           ( ( v2_tex_2 @ B @ A ) <=>
% 0.85/1.04             ( ![C:$i]:
% 0.85/1.04               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.04                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.85/1.04                      ( ![D:$i]:
% 0.85/1.04                        ( ( m1_subset_1 @
% 0.85/1.04                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.85/1.04                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.85/1.04                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.85/1.04                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.85/1.04  thf('33', plain,
% 0.85/1.04      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.85/1.04         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.85/1.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.85/1.04          | ~ (v3_pre_topc @ X26 @ X24)
% 0.85/1.04          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X26)
% 0.85/1.04              != (sk_C_1 @ X23 @ X24))
% 0.85/1.04          | (v2_tex_2 @ X23 @ X24)
% 0.85/1.04          | ~ (l1_pre_topc @ X24))),
% 0.85/1.04      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.85/1.04  thf('34', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         (~ (l1_pre_topc @ X0)
% 0.85/1.04          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.85/1.04          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.85/1.04              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.85/1.04          | ~ (v3_pre_topc @ X1 @ X0)
% 0.85/1.04          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['32', '33'])).
% 0.85/1.04  thf('35', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.85/1.04          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.85/1.04              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.85/1.04          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['31', '34'])).
% 0.85/1.04  thf('36', plain,
% 0.85/1.04      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.85/1.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.85/1.04  thf(redefinition_k9_subset_1, axiom,
% 0.85/1.04    (![A:$i,B:$i,C:$i]:
% 0.85/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.04       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.85/1.04  thf('37', plain,
% 0.85/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.85/1.04         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.85/1.04          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.85/1.04      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.85/1.04  thf('38', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.85/1.04           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['36', '37'])).
% 0.85/1.04  thf(t2_boole, axiom,
% 0.85/1.04    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.85/1.04  thf('39', plain,
% 0.85/1.04      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.85/1.04      inference('cnf', [status(esa)], [t2_boole])).
% 0.85/1.04  thf('40', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['38', '39'])).
% 0.85/1.04  thf('41', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.85/1.04          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.85/1.04          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0))),
% 0.85/1.04      inference('demod', [status(thm)], ['35', '40'])).
% 0.85/1.04  thf('42', plain,
% 0.85/1.04      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.85/1.04        | ~ (l1_pre_topc @ sk_A)
% 0.85/1.04        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.85/1.04        | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ sk_A)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['30', '41'])).
% 0.85/1.04  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.04  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('45', plain,
% 0.85/1.04      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.85/1.04      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.85/1.04  thf('46', plain,
% 0.85/1.04      (![X23 : $i, X24 : $i]:
% 0.85/1.04         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.85/1.04          | (r1_tarski @ (sk_C_1 @ X23 @ X24) @ X23)
% 0.85/1.04          | (v2_tex_2 @ X23 @ X24)
% 0.85/1.04          | ~ (l1_pre_topc @ X24))),
% 0.85/1.04      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.85/1.04  thf('47', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         (~ (l1_pre_topc @ X0)
% 0.85/1.04          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.85/1.04          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['45', '46'])).
% 0.85/1.04  thf('48', plain,
% 0.85/1.04      (![X0 : $i, X1 : $i]:
% 0.85/1.04         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['13', '14'])).
% 0.85/1.04  thf('49', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0)
% 0.85/1.04          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.85/1.04          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['47', '48'])).
% 0.85/1.04  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.04  thf('51', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.85/1.04          | ~ (l1_pre_topc @ X0)
% 0.85/1.04          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['49', '50'])).
% 0.85/1.04  thf('52', plain,
% 0.85/1.04      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.85/1.04      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.85/1.04  thf('53', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.85/1.04      inference('demod', [status(thm)], ['0', '3'])).
% 0.85/1.04  thf('54', plain,
% 0.85/1.04      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['52', '53'])).
% 0.85/1.04  thf('55', plain,
% 0.85/1.04      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.85/1.04        | ~ (l1_pre_topc @ sk_A)
% 0.85/1.04        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.85/1.04      inference('sup-', [status(thm)], ['51', '54'])).
% 0.85/1.04  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.85/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.85/1.04  thf('58', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.85/1.04  thf('59', plain,
% 0.85/1.04      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.85/1.04      inference('demod', [status(thm)], ['42', '43', '44', '58'])).
% 0.85/1.04  thf('60', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.85/1.04      inference('simplify', [status(thm)], ['59'])).
% 0.85/1.04  thf('61', plain, ($false), inference('demod', [status(thm)], ['4', '60'])).
% 0.85/1.04  
% 0.85/1.04  % SZS output end Refutation
% 0.85/1.04  
% 0.85/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

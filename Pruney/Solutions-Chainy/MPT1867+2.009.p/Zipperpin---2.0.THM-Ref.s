%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uHLYWMASQ3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:27 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 224 expanded)
%              Number of leaves         :   29 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  614 (1920 expanded)
%              Number of equality atoms :   30 (  83 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('9',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
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

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X29 @ X30 ) @ X29 )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
        = ( sk_C_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','20'])).

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

thf('22',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k1_xboole_0
      = ( sk_C_1 @ k1_xboole_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( k1_xboole_0
    = ( sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( sk_C_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X29: $i,X30: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X32 @ X30 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ X32 )
       != ( sk_C_1 @ X29 @ X30 ) )
      | ( v2_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C_1 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ( v2_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 )
       != ( sk_C_1 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A ) )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( k1_xboole_0
    = ( sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('38',plain,
    ( k1_xboole_0
    = ( sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( k1_xboole_0
    = ( sk_C_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 )
       != k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','42'])).

thf('44',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X15 @ X14 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('50',plain,(
    ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','50'])).

thf('52',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','24'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['51','54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uHLYWMASQ3
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.77/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.99  % Solved by: fo/fo7.sh
% 0.77/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.99  % done 1179 iterations in 0.549s
% 0.77/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.99  % SZS output start Refutation
% 0.77/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.99  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.77/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.99  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.77/0.99  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.77/0.99  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.77/0.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.77/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.99  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.77/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.99  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.99  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.77/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.99  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.99  thf(d3_tarski, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( r1_tarski @ A @ B ) <=>
% 0.77/0.99       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/0.99  thf('0', plain,
% 0.77/0.99      (![X6 : $i, X8 : $i]:
% 0.77/0.99         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.77/0.99      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.99  thf(d1_xboole_0, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.77/0.99  thf('1', plain,
% 0.77/0.99      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.77/0.99      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.77/0.99  thf('2', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['0', '1'])).
% 0.77/0.99  thf(t3_subset, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/0.99  thf('3', plain,
% 0.77/0.99      (![X18 : $i, X20 : $i]:
% 0.77/0.99         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.77/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.99  thf('4', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.99  thf(cc1_tops_1, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.77/0.99  thf('5', plain,
% 0.77/0.99      (![X27 : $i, X28 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.77/0.99          | (v3_pre_topc @ X27 @ X28)
% 0.77/0.99          | ~ (v1_xboole_0 @ X27)
% 0.77/0.99          | ~ (l1_pre_topc @ X28)
% 0.77/0.99          | ~ (v2_pre_topc @ X28))),
% 0.77/0.99      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.77/0.99  thf('6', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (~ (v1_xboole_0 @ X1)
% 0.77/0.99          | ~ (v2_pre_topc @ X0)
% 0.77/0.99          | ~ (l1_pre_topc @ X0)
% 0.77/0.99          | ~ (v1_xboole_0 @ X1)
% 0.77/0.99          | (v3_pre_topc @ X1 @ X0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.99  thf('7', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((v3_pre_topc @ X1 @ X0)
% 0.77/0.99          | ~ (l1_pre_topc @ X0)
% 0.77/0.99          | ~ (v2_pre_topc @ X0)
% 0.77/0.99          | ~ (v1_xboole_0 @ X1))),
% 0.77/0.99      inference('simplify', [status(thm)], ['6'])).
% 0.77/0.99  thf(t4_subset_1, axiom,
% 0.77/0.99    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.77/0.99  thf('8', plain,
% 0.77/0.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.99  thf('9', plain,
% 0.77/0.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.99  thf(d5_tex_2, axiom,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( l1_pre_topc @ A ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99           ( ( v2_tex_2 @ B @ A ) <=>
% 0.77/0.99             ( ![C:$i]:
% 0.77/0.99               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.77/0.99                      ( ![D:$i]:
% 0.77/0.99                        ( ( m1_subset_1 @
% 0.77/0.99                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.99                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.77/0.99                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.77/0.99                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.99  thf('10', plain,
% 0.77/0.99      (![X29 : $i, X30 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.77/0.99          | (r1_tarski @ (sk_C_1 @ X29 @ X30) @ X29)
% 0.77/0.99          | (v2_tex_2 @ X29 @ X30)
% 0.77/0.99          | ~ (l1_pre_topc @ X30))),
% 0.77/0.99      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.99  thf('11', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (~ (l1_pre_topc @ X0)
% 0.77/0.99          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.99          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['9', '10'])).
% 0.77/0.99  thf(t28_xboole_1, axiom,
% 0.77/0.99    (![A:$i,B:$i]:
% 0.77/0.99     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.99  thf('12', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.99  thf('13', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.99          | ~ (l1_pre_topc @ X0)
% 0.77/0.99          | ((k3_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.77/0.99              = (sk_C_1 @ k1_xboole_0 @ X0)))),
% 0.77/0.99      inference('sup-', [status(thm)], ['11', '12'])).
% 0.77/0.99  thf('14', plain,
% 0.77/0.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.99  thf('15', plain,
% 0.77/0.99      (![X18 : $i, X19 : $i]:
% 0.77/0.99         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.77/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.99  thf('16', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.77/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.77/0.99  thf('17', plain,
% 0.77/0.99      (![X12 : $i, X13 : $i]:
% 0.77/0.99         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.77/0.99      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.99  thf('18', plain,
% 0.77/0.99      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/0.99  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.99    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.99  thf('19', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.99      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.99  thf('20', plain,
% 0.77/0.99      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.99      inference('sup+', [status(thm)], ['18', '19'])).
% 0.77/0.99  thf('21', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.99          | ~ (l1_pre_topc @ X0)
% 0.77/0.99          | ((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ X0)))),
% 0.77/0.99      inference('demod', [status(thm)], ['13', '20'])).
% 0.77/0.99  thf(t35_tex_2, conjecture,
% 0.77/0.99    (![A:$i]:
% 0.77/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.99       ( ![B:$i]:
% 0.77/0.99         ( ( ( v1_xboole_0 @ B ) & 
% 0.77/0.99             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.99           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.77/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.99    (~( ![A:$i]:
% 0.77/0.99        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.77/0.99            ( l1_pre_topc @ A ) ) =>
% 0.77/0.99          ( ![B:$i]:
% 0.77/0.99            ( ( ( v1_xboole_0 @ B ) & 
% 0.77/0.99                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.77/0.99              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.77/0.99    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.77/0.99  thf('22', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('23', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf(l13_xboole_0, axiom,
% 0.77/0.99    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.99  thf('24', plain,
% 0.77/0.99      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 0.77/0.99      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.99  thf('25', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.99  thf('26', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.77/0.99      inference('demod', [status(thm)], ['22', '25'])).
% 0.77/0.99  thf('27', plain,
% 0.77/0.99      ((((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ sk_A))
% 0.77/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.99      inference('sup-', [status(thm)], ['21', '26'])).
% 0.77/0.99  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('29', plain, (((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.99  thf('30', plain,
% 0.77/0.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.99  thf('31', plain,
% 0.77/0.99      (![X29 : $i, X30 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.77/0.99          | (m1_subset_1 @ (sk_C_1 @ X29 @ X30) @ 
% 0.77/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.77/0.99          | (v2_tex_2 @ X29 @ X30)
% 0.77/0.99          | ~ (l1_pre_topc @ X30))),
% 0.77/0.99      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.99  thf('32', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (~ (l1_pre_topc @ X0)
% 0.77/0.99          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.99          | (m1_subset_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.77/0.99             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['30', '31'])).
% 0.77/0.99  thf('33', plain,
% 0.77/0.99      (![X29 : $i, X30 : $i, X32 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.77/0.99          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.77/0.99          | ~ (v3_pre_topc @ X32 @ X30)
% 0.77/0.99          | ((k9_subset_1 @ (u1_struct_0 @ X30) @ X29 @ X32)
% 0.77/0.99              != (sk_C_1 @ X29 @ X30))
% 0.77/0.99          | (v2_tex_2 @ X29 @ X30)
% 0.77/0.99          | ~ (l1_pre_topc @ X30))),
% 0.77/0.99      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.99  thf('34', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.77/0.99          | ~ (l1_pre_topc @ X0)
% 0.77/0.99          | ~ (l1_pre_topc @ X0)
% 0.77/0.99          | (v2_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.77/0.99          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.77/0.99              X1) != (sk_C_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0))
% 0.77/0.99          | ~ (v3_pre_topc @ X1 @ X0)
% 0.77/0.99          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.99  thf('35', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.77/0.99          | ~ (v3_pre_topc @ X1 @ X0)
% 0.77/0.99          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C_1 @ k1_xboole_0 @ X0) @ 
% 0.77/0.99              X1) != (sk_C_1 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0))
% 0.77/0.99          | (v2_tex_2 @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.77/0.99          | ~ (l1_pre_topc @ X0)
% 0.77/0.99          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.77/0.99      inference('simplify', [status(thm)], ['34'])).
% 0.77/0.99  thf('36', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ X0)
% 0.77/0.99            != (sk_C_1 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A))
% 0.77/0.99          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.77/0.99          | ~ (l1_pre_topc @ sk_A)
% 0.77/0.99          | (v2_tex_2 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.77/0.99          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.77/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.99      inference('sup-', [status(thm)], ['29', '35'])).
% 0.77/0.99  thf('37', plain, (((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.99  thf('38', plain, (((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.99  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('40', plain, (((k1_xboole_0) = (sk_C_1 @ k1_xboole_0 @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.99  thf('41', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ X0)
% 0.77/0.99            != (k1_xboole_0))
% 0.77/0.99          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.77/0.99          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.77/0.99          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.77/0.99          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.99      inference('demod', [status(thm)], ['36', '37', '38', '39', '40'])).
% 0.77/0.99  thf('42', plain,
% 0.77/0.99      (![X0 : $i]:
% 0.77/0.99         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.99          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.77/0.99          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.77/0.99          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ X0)
% 0.77/0.99              != (k1_xboole_0)))),
% 0.77/0.99      inference('simplify', [status(thm)], ['41'])).
% 0.77/0.99  thf('43', plain,
% 0.77/0.99      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ k1_xboole_0)
% 0.77/0.99          != (k1_xboole_0))
% 0.77/0.99        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.77/0.99        | ~ (v3_pre_topc @ k1_xboole_0 @ sk_A))),
% 0.77/0.99      inference('sup-', [status(thm)], ['8', '42'])).
% 0.77/0.99  thf('44', plain,
% 0.77/0.99      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.77/0.99      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.99  thf(idempotence_k9_subset_1, axiom,
% 0.77/0.99    (![A:$i,B:$i,C:$i]:
% 0.77/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.99       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.77/0.99  thf('45', plain,
% 0.77/0.99      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.77/0.99         (((k9_subset_1 @ X15 @ X14 @ X14) = (X14))
% 0.77/0.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.77/0.99      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.77/0.99  thf('46', plain,
% 0.77/0.99      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.77/0.99      inference('sup-', [status(thm)], ['44', '45'])).
% 0.77/0.99  thf('47', plain,
% 0.77/0.99      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.99        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.77/0.99        | ~ (v3_pre_topc @ k1_xboole_0 @ sk_A))),
% 0.77/0.99      inference('demod', [status(thm)], ['43', '46'])).
% 0.77/0.99  thf('48', plain,
% 0.77/0.99      ((~ (v3_pre_topc @ k1_xboole_0 @ sk_A) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.77/0.99      inference('simplify', [status(thm)], ['47'])).
% 0.77/0.99  thf('49', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.77/0.99      inference('demod', [status(thm)], ['22', '25'])).
% 0.77/0.99  thf('50', plain, (~ (v3_pre_topc @ k1_xboole_0 @ sk_A)),
% 0.77/0.99      inference('clc', [status(thm)], ['48', '49'])).
% 0.77/0.99  thf('51', plain,
% 0.77/0.99      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.77/0.99        | ~ (v2_pre_topc @ sk_A)
% 0.77/0.99        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.99      inference('sup-', [status(thm)], ['7', '50'])).
% 0.77/0.99  thf('52', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('53', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.77/0.99      inference('sup-', [status(thm)], ['23', '24'])).
% 0.77/0.99  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.99      inference('demod', [status(thm)], ['52', '53'])).
% 0.77/0.99  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.99  thf('57', plain, ($false),
% 0.77/0.99      inference('demod', [status(thm)], ['51', '54', '55', '56'])).
% 0.77/0.99  
% 0.77/0.99  % SZS output end Refutation
% 0.77/0.99  
% 0.77/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

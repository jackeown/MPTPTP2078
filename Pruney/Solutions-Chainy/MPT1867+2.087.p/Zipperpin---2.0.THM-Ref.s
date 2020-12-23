%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cfB9HrhAf7

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:38 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 155 expanded)
%              Number of leaves         :   30 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  589 (1179 expanded)
%              Number of equality atoms :   30 (  48 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
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

thf('23',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X23 )
       != ( sk_C @ X20 @ X21 ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['25','45'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('51',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('61',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48','49','61'])).

thf('63',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['4','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cfB9HrhAf7
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:52:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 401 iterations in 0.201s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.65  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.65  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.65  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.65  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.65  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.46/0.65  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.65  thf(t35_tex_2, conjecture,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.65             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i]:
% 0.46/0.65        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.65            ( l1_pre_topc @ A ) ) =>
% 0.46/0.65          ( ![B:$i]:
% 0.46/0.65            ( ( ( v1_xboole_0 @ B ) & 
% 0.46/0.65                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.46/0.65  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(l13_xboole_0, axiom,
% 0.46/0.65    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.65  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('6', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf(t4_subset_1, axiom,
% 0.46/0.65    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf(t44_tops_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      (![X18 : $i, X19 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.46/0.65          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ X18)
% 0.46/0.65          | ~ (l1_pre_topc @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.65  thf(t3_xboole_1, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.65  thf('11', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.65  thf('12', plain,
% 0.46/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf(fc9_tops_1, axiom,
% 0.46/0.65    (![A:$i,B:$i]:
% 0.46/0.65     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.65         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.65       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.46/0.65  thf('13', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X16)
% 0.46/0.65          | ~ (v2_pre_topc @ X16)
% 0.46/0.65          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.46/0.65          | (v3_pre_topc @ (k1_tops_1 @ X16 @ X17) @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.46/0.65  thf('14', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v3_pre_topc @ (k1_tops_1 @ X0 @ k1_xboole_0) @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ~ (v2_pre_topc @ X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['11', '14'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_pre_topc @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.46/0.65      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((v3_pre_topc @ X0 @ X1)
% 0.46/0.65          | ~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X1)
% 0.46/0.65          | ~ (v2_pre_topc @ X1))),
% 0.46/0.65      inference('sup+', [status(thm)], ['6', '16'])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v2_pre_topc @ sk_A)
% 0.46/0.65          | ~ (v1_xboole_0 @ X0)
% 0.46/0.65          | (v3_pre_topc @ X0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '17'])).
% 0.46/0.65  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('20', plain,
% 0.46/0.65      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['18', '19'])).
% 0.46/0.65  thf('21', plain,
% 0.46/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf('22', plain,
% 0.46/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf(d5_tex_2, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ( l1_pre_topc @ A ) =>
% 0.46/0.65       ( ![B:$i]:
% 0.46/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65           ( ( v2_tex_2 @ B @ A ) <=>
% 0.46/0.65             ( ![C:$i]:
% 0.46/0.65               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.46/0.65                      ( ![D:$i]:
% 0.46/0.65                        ( ( m1_subset_1 @
% 0.46/0.65                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.65                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.46/0.65                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.46/0.65                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.65          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.65          | ~ (v3_pre_topc @ X23 @ X21)
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X23)
% 0.46/0.65              != (sk_C @ X20 @ X21))
% 0.46/0.65          | (v2_tex_2 @ X20 @ X21)
% 0.46/0.65          | ~ (l1_pre_topc @ X21))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.46/0.65              != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.65          | ~ (v3_pre_topc @ X1 @ X0)
% 0.46/0.65          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.46/0.65          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.46/0.65              != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.65          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '24'])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.65  thf('27', plain,
% 0.46/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.65         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.46/0.65          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.65      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.65  thf('28', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.46/0.65           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('29', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('30', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.65  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf(t7_xboole_0, axiom,
% 0.46/0.65    (![A:$i]:
% 0.46/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.46/0.65      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf(dt_k9_subset_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.65       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.46/0.65          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.46/0.65      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 0.46/0.65          (k1_zfmisc_1 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.65  thf(t5_subset, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i]:
% 0.46/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X13 @ X14)
% 0.46/0.65          | ~ (v1_xboole_0 @ X15)
% 0.46/0.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X2 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.46/0.65           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.46/0.65          | ~ (v1_xboole_0 @ X0)
% 0.46/0.65          | ~ (v1_xboole_0 @ X3))),
% 0.46/0.65      inference('sup-', [status(thm)], ['33', '40'])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.65         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('condensation', [status(thm)], ['41'])).
% 0.46/0.65  thf('43', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['32', '42'])).
% 0.46/0.65  thf('44', plain,
% 0.46/0.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['31', '43'])).
% 0.46/0.65  thf('45', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i]:
% 0.46/0.65         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['28', '44'])).
% 0.46/0.65  thf('46', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.46/0.65          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.46/0.65          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0))),
% 0.46/0.65      inference('demod', [status(thm)], ['25', '45'])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['20', '46'])).
% 0.46/0.65  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.46/0.65      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X20 : $i, X21 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.46/0.65          | (r1_tarski @ (sk_C @ X20 @ X21) @ X20)
% 0.46/0.65          | (v2_tex_2 @ X20 @ X21)
% 0.46/0.65          | ~ (l1_pre_topc @ X21))),
% 0.46/0.65      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (l1_pre_topc @ X0)
% 0.46/0.65          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.65          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['50', '51'])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.46/0.65          | ~ (l1_pre_topc @ X0)
% 0.46/0.65          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '53'])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.46/0.65  thf('56', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.65  thf('58', plain,
% 0.46/0.65      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.46/0.65        | ~ (l1_pre_topc @ sk_A)
% 0.46/0.65        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['54', '57'])).
% 0.46/0.65  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.65  thf('61', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.46/0.65      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.46/0.65      inference('demod', [status(thm)], ['47', '48', '49', '61'])).
% 0.46/0.65  thf('63', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('simplify', [status(thm)], ['62'])).
% 0.46/0.65  thf('64', plain, ($false), inference('demod', [status(thm)], ['4', '63'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

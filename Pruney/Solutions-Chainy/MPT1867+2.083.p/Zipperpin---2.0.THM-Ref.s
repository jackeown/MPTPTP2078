%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.61t5FrmUAS

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:37 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 144 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :   17
%              Number of atoms          :  599 (1156 expanded)
%              Number of equality atoms :   41 (  58 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
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

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r1_tarski @ ( sk_C @ X17 @ X18 ) @ X17 )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('11',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','19'])).

thf(rc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( v3_pre_topc @ ( sk_B @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('22',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[rc3_tops_1])).

thf('23',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X20 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X20 )
       != ( sk_C @ X17 @ X18 ) )
      | ( v2_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('35',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('36',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('41',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['25','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('59',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.61t5FrmUAS
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:00:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.74  % Solved by: fo/fo7.sh
% 0.53/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.74  % done 741 iterations in 0.289s
% 0.53/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.74  % SZS output start Refutation
% 0.53/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.74  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.53/0.74  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.53/0.74  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.74  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.53/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.74  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.53/0.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.74  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.53/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.74  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.53/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.74  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.53/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.74  thf(t35_tex_2, conjecture,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( ( v1_xboole_0 @ B ) & 
% 0.53/0.74             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.74           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.53/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.74    (~( ![A:$i]:
% 0.53/0.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.53/0.74            ( l1_pre_topc @ A ) ) =>
% 0.53/0.74          ( ![B:$i]:
% 0.53/0.74            ( ( ( v1_xboole_0 @ B ) & 
% 0.53/0.74                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.74              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.53/0.74    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.53/0.74  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf(l13_xboole_0, axiom,
% 0.53/0.74    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.74  thf('1', plain,
% 0.53/0.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf(t4_subset_1, axiom,
% 0.53/0.74    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.53/0.74  thf('2', plain,
% 0.53/0.74      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.74  thf(d5_tex_2, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( l1_pre_topc @ A ) =>
% 0.53/0.74       ( ![B:$i]:
% 0.53/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74           ( ( v2_tex_2 @ B @ A ) <=>
% 0.53/0.74             ( ![C:$i]:
% 0.53/0.74               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.53/0.74                      ( ![D:$i]:
% 0.53/0.74                        ( ( m1_subset_1 @
% 0.53/0.74                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.74                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.53/0.74                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.53/0.74                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.74  thf('3', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.53/0.74          | (r1_tarski @ (sk_C @ X17 @ X18) @ X17)
% 0.53/0.74          | (v2_tex_2 @ X17 @ X18)
% 0.53/0.74          | ~ (l1_pre_topc @ X18))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.53/0.74  thf('4', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (~ (l1_pre_topc @ X0)
% 0.53/0.74          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.53/0.74          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.74  thf(t3_xboole_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.74  thf('5', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.53/0.74  thf('6', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.53/0.74          | ~ (l1_pre_topc @ X0)
% 0.53/0.74          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.53/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.53/0.74  thf('7', plain,
% 0.53/0.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('8', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('9', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('10', plain,
% 0.53/0.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.74      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.53/0.74  thf('11', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.53/0.74      inference('demod', [status(thm)], ['8', '11'])).
% 0.53/0.74  thf('13', plain,
% 0.53/0.74      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['7', '12'])).
% 0.53/0.74  thf('14', plain,
% 0.53/0.74      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.53/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.53/0.74        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['6', '13'])).
% 0.53/0.74  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('16', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('17', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.74  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['16', '17'])).
% 0.53/0.74  thf('19', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['14', '15', '18'])).
% 0.53/0.74  thf('20', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['1', '19'])).
% 0.53/0.74  thf(rc3_tops_1, axiom,
% 0.53/0.74    (![A:$i]:
% 0.53/0.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.74       ( ?[B:$i]:
% 0.53/0.74         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.53/0.74           ( ~( v1_xboole_0 @ B ) ) & 
% 0.53/0.74           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.53/0.74  thf('21', plain,
% 0.53/0.74      (![X16 : $i]:
% 0.53/0.74         ((v3_pre_topc @ (sk_B @ X16) @ X16)
% 0.53/0.74          | ~ (l1_pre_topc @ X16)
% 0.53/0.74          | ~ (v2_pre_topc @ X16)
% 0.53/0.74          | (v2_struct_0 @ X16))),
% 0.53/0.74      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.53/0.74  thf('22', plain,
% 0.53/0.74      (![X16 : $i]:
% 0.53/0.74         ((m1_subset_1 @ (sk_B @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.53/0.74          | ~ (l1_pre_topc @ X16)
% 0.53/0.74          | ~ (v2_pre_topc @ X16)
% 0.53/0.74          | (v2_struct_0 @ X16))),
% 0.53/0.74      inference('cnf', [status(esa)], [rc3_tops_1])).
% 0.53/0.74  thf('23', plain,
% 0.53/0.74      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.74  thf('24', plain,
% 0.53/0.74      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.53/0.74         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.53/0.74          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.53/0.74          | ~ (v3_pre_topc @ X20 @ X18)
% 0.53/0.74          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X20)
% 0.53/0.74              != (sk_C @ X17 @ X18))
% 0.53/0.74          | (v2_tex_2 @ X17 @ X18)
% 0.53/0.74          | ~ (l1_pre_topc @ X18))),
% 0.53/0.74      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.53/0.74  thf('25', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (l1_pre_topc @ X0)
% 0.53/0.74          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.53/0.74          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.53/0.74              != (sk_C @ k1_xboole_0 @ X0))
% 0.53/0.74          | ~ (v3_pre_topc @ X1 @ X0)
% 0.53/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.53/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.53/0.74  thf('26', plain,
% 0.53/0.74      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.74  thf(commutativity_k9_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.53/0.74  thf('27', plain,
% 0.53/0.74      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.53/0.74         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.53/0.74          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.53/0.74      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.53/0.74  thf('28', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.53/0.74           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf('29', plain,
% 0.53/0.74      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.53/0.74      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.53/0.74  thf(redefinition_k9_subset_1, axiom,
% 0.53/0.74    (![A:$i,B:$i,C:$i]:
% 0.53/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.74       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.53/0.74  thf('30', plain,
% 0.53/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.74         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.53/0.74          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.53/0.74  thf('31', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.53/0.74           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.74  thf('32', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.53/0.74           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['28', '31'])).
% 0.53/0.74  thf('33', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.53/0.74           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.53/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.53/0.74  thf(dt_k2_subset_1, axiom,
% 0.53/0.74    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.53/0.74  thf('34', plain,
% 0.53/0.74      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.53/0.74      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.53/0.74  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.53/0.74  thf('35', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.53/0.74      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.53/0.74  thf('36', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.53/0.74      inference('demod', [status(thm)], ['34', '35'])).
% 0.53/0.74  thf('37', plain,
% 0.53/0.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.74         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.53/0.74          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.74      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.53/0.74  thf('38', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.74  thf('39', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((k9_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 0.53/0.74           = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.74      inference('sup+', [status(thm)], ['33', '38'])).
% 0.53/0.74  thf(t17_xboole_1, axiom,
% 0.53/0.74    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.74  thf('40', plain,
% 0.53/0.74      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.53/0.74      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.74  thf('41', plain,
% 0.53/0.74      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.53/0.74      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.53/0.74  thf('42', plain,
% 0.53/0.74      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['40', '41'])).
% 0.53/0.74  thf('43', plain,
% 0.53/0.74      (![X0 : $i]: ((k9_subset_1 @ X0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['39', '42'])).
% 0.53/0.74  thf('44', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.53/0.74           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.74  thf('45', plain,
% 0.53/0.74      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.53/0.74  thf('46', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.53/0.74      inference('demod', [status(thm)], ['32', '45'])).
% 0.53/0.74  thf('47', plain,
% 0.53/0.74      (![X0 : $i, X1 : $i]:
% 0.53/0.74         (~ (l1_pre_topc @ X0)
% 0.53/0.74          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.53/0.74          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.53/0.74          | ~ (v3_pre_topc @ X1 @ X0)
% 0.53/0.74          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.53/0.74      inference('demod', [status(thm)], ['25', '46'])).
% 0.53/0.74  thf('48', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v2_struct_0 @ X0)
% 0.53/0.74          | ~ (v2_pre_topc @ X0)
% 0.53/0.74          | ~ (l1_pre_topc @ X0)
% 0.53/0.74          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.53/0.74          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.53/0.74          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.53/0.74          | ~ (l1_pre_topc @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['22', '47'])).
% 0.53/0.74  thf('49', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.53/0.74          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.53/0.74          | ~ (v3_pre_topc @ (sk_B @ X0) @ X0)
% 0.53/0.74          | ~ (l1_pre_topc @ X0)
% 0.53/0.74          | ~ (v2_pre_topc @ X0)
% 0.53/0.74          | (v2_struct_0 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['48'])).
% 0.53/0.74  thf('50', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v2_struct_0 @ X0)
% 0.53/0.74          | ~ (v2_pre_topc @ X0)
% 0.53/0.74          | ~ (l1_pre_topc @ X0)
% 0.53/0.74          | (v2_struct_0 @ X0)
% 0.53/0.74          | ~ (v2_pre_topc @ X0)
% 0.53/0.74          | ~ (l1_pre_topc @ X0)
% 0.53/0.74          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.53/0.74          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.53/0.74      inference('sup-', [status(thm)], ['21', '49'])).
% 0.53/0.74  thf('51', plain,
% 0.53/0.74      (![X0 : $i]:
% 0.53/0.74         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.53/0.74          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.53/0.74          | ~ (l1_pre_topc @ X0)
% 0.53/0.74          | ~ (v2_pre_topc @ X0)
% 0.53/0.74          | (v2_struct_0 @ X0))),
% 0.53/0.74      inference('simplify', [status(thm)], ['50'])).
% 0.53/0.74  thf('52', plain,
% 0.53/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.74        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.53/0.74        | (v2_struct_0 @ sk_A)
% 0.53/0.74        | ~ (v2_pre_topc @ sk_A)
% 0.53/0.74        | ~ (l1_pre_topc @ sk_A)
% 0.53/0.74        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.53/0.74      inference('sup-', [status(thm)], ['20', '51'])).
% 0.53/0.74  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.74      inference('demod', [status(thm)], ['16', '17'])).
% 0.53/0.74  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.74  thf('56', plain,
% 0.53/0.74      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.74        | (v2_struct_0 @ sk_A)
% 0.53/0.74        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.53/0.74      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.53/0.74  thf('57', plain, (((v2_tex_2 @ k1_xboole_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.53/0.74      inference('simplify', [status(thm)], ['56'])).
% 0.53/0.74  thf('58', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.53/0.74      inference('demod', [status(thm)], ['8', '11'])).
% 0.53/0.74  thf('59', plain, ((v2_struct_0 @ sk_A)),
% 0.53/0.74      inference('clc', [status(thm)], ['57', '58'])).
% 0.53/0.74  thf('60', plain, ($false), inference('demod', [status(thm)], ['0', '59'])).
% 0.53/0.74  
% 0.53/0.74  % SZS output end Refutation
% 0.53/0.74  
% 0.53/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

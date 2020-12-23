%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TS8cshVsgD

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:38 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 157 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  657 (1365 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A_1 ) ),
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
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ sk_A_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != X18 )
      | ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('17',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 )
        | ( ( k1_tops_1 @ X19 @ X18 )
         != X18 )
        | ( v3_pre_topc @ X18 @ X19 ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 )
        | ( ( k1_tops_1 @ X19 @ X18 )
         != X18 )
        | ( v3_pre_topc @ X18 @ X19 ) ) ),
    inference(split,[status(esa)],['16'])).

thf(existence_l1_pre_topc,axiom,(
    ? [A: $i] :
      ( l1_pre_topc @ A ) )).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[existence_l1_pre_topc])).

thf('19',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('21',plain,
    ( ! [X0: $i] :
        ~ ( l1_pre_topc @ X0 )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 )
        | ( ( k1_tops_1 @ X19 @ X18 )
         != X18 )
        | ( v3_pre_topc @ X18 @ X19 ) )
    | ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('24',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != X18 )
      | ( v3_pre_topc @ X18 @ X19 ) ) ),
    inference('sat_resolution*',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != X18 )
      | ( v3_pre_topc @ X18 @ X19 ) ) ),
    inference(simpl_trail,[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k1_tops_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v2_pre_topc @ sk_A_1 )
    | ( v3_pre_topc @ k1_xboole_0 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['14','26'])).

thf('28',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v3_pre_topc @ k1_xboole_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['27','30','31','32'])).

thf('34',plain,(
    v3_pre_topc @ k1_xboole_0 @ sk_A_1 ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ X0 @ sk_A_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','34'])).

thf('36',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('37',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
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

thf('38',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X23 )
       != ( sk_C @ X20 @ X21 ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['40','43','46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A_1 )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('50',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A_1 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A_1 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['28','29'])).

thf('62',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A_1 )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','50','62'])).

thf('64',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A_1 ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['4','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TS8cshVsgD
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:07:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.74/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.96  % Solved by: fo/fo7.sh
% 0.74/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.96  % done 836 iterations in 0.501s
% 0.74/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.96  % SZS output start Refutation
% 0.74/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.74/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.74/0.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.74/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.96  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.74/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.96  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.74/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.74/0.96  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.74/0.96  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.74/0.96  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.74/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.96  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.74/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.96  thf(t35_tex_2, conjecture,
% 0.74/0.96    (![A:$i]:
% 0.74/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.74/0.96       ( ![B:$i]:
% 0.74/0.96         ( ( ( v1_xboole_0 @ B ) & 
% 0.74/0.96             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.96           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.74/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.96    (~( ![A:$i]:
% 0.74/0.96        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.74/0.96            ( l1_pre_topc @ A ) ) =>
% 0.74/0.96          ( ![B:$i]:
% 0.74/0.96            ( ( ( v1_xboole_0 @ B ) & 
% 0.74/0.96                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.96              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.74/0.96    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.74/0.96  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf(l13_xboole_0, axiom,
% 0.74/0.96    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.74/0.96  thf('2', plain,
% 0.74/0.96      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.74/0.96  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.96  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A_1)),
% 0.74/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.74/0.96  thf('5', plain,
% 0.74/0.96      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.74/0.96  thf('6', plain, ((l1_pre_topc @ sk_A_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('7', plain,
% 0.74/0.96      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.74/0.96  thf(t4_subset_1, axiom,
% 0.74/0.96    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.74/0.96  thf('8', plain,
% 0.74/0.96      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf(t44_tops_1, axiom,
% 0.74/0.96    (![A:$i]:
% 0.74/0.96     ( ( l1_pre_topc @ A ) =>
% 0.74/0.96       ( ![B:$i]:
% 0.74/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.96           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.74/0.96  thf('9', plain,
% 0.74/0.96      (![X14 : $i, X15 : $i]:
% 0.74/0.96         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.74/0.96          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ X14)
% 0.74/0.96          | ~ (l1_pre_topc @ X15))),
% 0.74/0.96      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.74/0.96  thf('10', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (~ (l1_pre_topc @ X0)
% 0.74/0.96          | (r1_tarski @ (k1_tops_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.74/0.96  thf(t3_xboole_1, axiom,
% 0.74/0.96    (![A:$i]:
% 0.74/0.96     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.74/0.96  thf('11', plain,
% 0.74/0.96      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.74/0.96  thf('12', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (~ (l1_pre_topc @ X0)
% 0.74/0.96          | ((k1_tops_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/0.96  thf('13', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         (((k1_tops_1 @ X1 @ X0) = (k1_xboole_0))
% 0.74/0.96          | ~ (v1_xboole_0 @ X0)
% 0.74/0.96          | ~ (l1_pre_topc @ X1))),
% 0.74/0.96      inference('sup+', [status(thm)], ['7', '12'])).
% 0.74/0.96  thf('14', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (~ (v1_xboole_0 @ X0) | ((k1_tops_1 @ sk_A_1 @ X0) = (k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['6', '13'])).
% 0.74/0.96  thf('15', plain,
% 0.74/0.96      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf(t55_tops_1, axiom,
% 0.74/0.96    (![A:$i]:
% 0.74/0.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.74/0.96       ( ![B:$i]:
% 0.74/0.96         ( ( l1_pre_topc @ B ) =>
% 0.74/0.96           ( ![C:$i]:
% 0.74/0.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.96               ( ![D:$i]:
% 0.74/0.96                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.74/0.96                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.74/0.96                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.74/0.96                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.74/0.96                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.74/0.96  thf('16', plain,
% 0.74/0.96      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.74/0.96         (~ (l1_pre_topc @ X16)
% 0.74/0.96          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.74/0.96          | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.74/0.96          | (v3_pre_topc @ X18 @ X19)
% 0.74/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.74/0.96          | ~ (l1_pre_topc @ X19)
% 0.74/0.96          | ~ (v2_pre_topc @ X19))),
% 0.74/0.96      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.74/0.96  thf('17', plain,
% 0.74/0.96      ((![X18 : $i, X19 : $i]:
% 0.74/0.96          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.74/0.96           | ~ (l1_pre_topc @ X19)
% 0.74/0.96           | ~ (v2_pre_topc @ X19)
% 0.74/0.96           | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.74/0.96           | (v3_pre_topc @ X18 @ X19)))
% 0.74/0.96         <= ((![X18 : $i, X19 : $i]:
% 0.74/0.96                (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.74/0.96                 | ~ (l1_pre_topc @ X19)
% 0.74/0.96                 | ~ (v2_pre_topc @ X19)
% 0.74/0.96                 | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.74/0.96                 | (v3_pre_topc @ X18 @ X19))))),
% 0.74/0.96      inference('split', [status(esa)], ['16'])).
% 0.74/0.96  thf(existence_l1_pre_topc, axiom, (?[A:$i]: ( l1_pre_topc @ A ))).
% 0.74/0.96  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.96      inference('cnf', [status(esa)], [existence_l1_pre_topc])).
% 0.74/0.96  thf('19', plain,
% 0.74/0.96      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf('20', plain,
% 0.74/0.96      ((![X16 : $i, X17 : $i]:
% 0.74/0.96          (~ (l1_pre_topc @ X16)
% 0.74/0.96           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))
% 0.74/0.96         <= ((![X16 : $i, X17 : $i]:
% 0.74/0.96                (~ (l1_pre_topc @ X16)
% 0.74/0.96                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))))),
% 0.74/0.96      inference('split', [status(esa)], ['16'])).
% 0.74/0.96  thf('21', plain,
% 0.74/0.96      ((![X0 : $i]: ~ (l1_pre_topc @ X0))
% 0.74/0.96         <= ((![X16 : $i, X17 : $i]:
% 0.74/0.96                (~ (l1_pre_topc @ X16)
% 0.74/0.96                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['19', '20'])).
% 0.74/0.96  thf('22', plain,
% 0.74/0.96      (~
% 0.74/0.96       (![X16 : $i, X17 : $i]:
% 0.74/0.96          (~ (l1_pre_topc @ X16)
% 0.74/0.96           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['18', '21'])).
% 0.74/0.96  thf('23', plain,
% 0.74/0.96      ((![X18 : $i, X19 : $i]:
% 0.74/0.96          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.74/0.96           | ~ (l1_pre_topc @ X19)
% 0.74/0.96           | ~ (v2_pre_topc @ X19)
% 0.74/0.96           | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.74/0.96           | (v3_pre_topc @ X18 @ X19))) | 
% 0.74/0.96       (![X16 : $i, X17 : $i]:
% 0.74/0.96          (~ (l1_pre_topc @ X16)
% 0.74/0.96           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))))),
% 0.74/0.96      inference('split', [status(esa)], ['16'])).
% 0.74/0.96  thf('24', plain,
% 0.74/0.96      ((![X18 : $i, X19 : $i]:
% 0.74/0.96          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.74/0.96           | ~ (l1_pre_topc @ X19)
% 0.74/0.96           | ~ (v2_pre_topc @ X19)
% 0.74/0.96           | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.74/0.96           | (v3_pre_topc @ X18 @ X19)))),
% 0.74/0.96      inference('sat_resolution*', [status(thm)], ['22', '23'])).
% 0.74/0.96  thf('25', plain,
% 0.74/0.96      (![X18 : $i, X19 : $i]:
% 0.74/0.96         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.74/0.96          | ~ (l1_pre_topc @ X19)
% 0.74/0.96          | ~ (v2_pre_topc @ X19)
% 0.74/0.96          | ((k1_tops_1 @ X19 @ X18) != (X18))
% 0.74/0.96          | (v3_pre_topc @ X18 @ X19))),
% 0.74/0.96      inference('simpl_trail', [status(thm)], ['17', '24'])).
% 0.74/0.96  thf('26', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         ((v3_pre_topc @ k1_xboole_0 @ X0)
% 0.74/0.96          | ((k1_tops_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.74/0.96          | ~ (v2_pre_topc @ X0)
% 0.74/0.96          | ~ (l1_pre_topc @ X0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['15', '25'])).
% 0.74/0.96  thf('27', plain,
% 0.74/0.96      ((((k1_xboole_0) != (k1_xboole_0))
% 0.74/0.96        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.74/0.96        | ~ (l1_pre_topc @ sk_A_1)
% 0.74/0.96        | ~ (v2_pre_topc @ sk_A_1)
% 0.74/0.96        | (v3_pre_topc @ k1_xboole_0 @ sk_A_1))),
% 0.74/0.96      inference('sup-', [status(thm)], ['14', '26'])).
% 0.74/0.96  thf('28', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('29', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.96  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.96      inference('demod', [status(thm)], ['28', '29'])).
% 0.74/0.96  thf('31', plain, ((l1_pre_topc @ sk_A_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('32', plain, ((v2_pre_topc @ sk_A_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('33', plain,
% 0.74/0.96      ((((k1_xboole_0) != (k1_xboole_0)) | (v3_pre_topc @ k1_xboole_0 @ sk_A_1))),
% 0.74/0.96      inference('demod', [status(thm)], ['27', '30', '31', '32'])).
% 0.74/0.96  thf('34', plain, ((v3_pre_topc @ k1_xboole_0 @ sk_A_1)),
% 0.74/0.96      inference('simplify', [status(thm)], ['33'])).
% 0.74/0.96  thf('35', plain,
% 0.74/0.96      (![X0 : $i]: ((v3_pre_topc @ X0 @ sk_A_1) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('sup+', [status(thm)], ['5', '34'])).
% 0.74/0.96  thf('36', plain,
% 0.74/0.96      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf('37', plain,
% 0.74/0.96      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf(d5_tex_2, axiom,
% 0.74/0.96    (![A:$i]:
% 0.74/0.96     ( ( l1_pre_topc @ A ) =>
% 0.74/0.96       ( ![B:$i]:
% 0.74/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.96           ( ( v2_tex_2 @ B @ A ) <=>
% 0.74/0.96             ( ![C:$i]:
% 0.74/0.96               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.96                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.74/0.96                      ( ![D:$i]:
% 0.74/0.96                        ( ( m1_subset_1 @
% 0.74/0.96                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.96                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.74/0.96                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.74/0.96                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.74/0.96  thf('38', plain,
% 0.74/0.96      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.74/0.96         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.74/0.96          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.74/0.96          | ~ (v3_pre_topc @ X23 @ X21)
% 0.74/0.96          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X23)
% 0.74/0.96              != (sk_C @ X20 @ X21))
% 0.74/0.96          | (v2_tex_2 @ X20 @ X21)
% 0.74/0.96          | ~ (l1_pre_topc @ X21))),
% 0.74/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.74/0.96  thf('39', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         (~ (l1_pre_topc @ X0)
% 0.74/0.96          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.74/0.96          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.74/0.96              != (sk_C @ k1_xboole_0 @ X0))
% 0.74/0.96          | ~ (v3_pre_topc @ X1 @ X0)
% 0.74/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.74/0.96      inference('sup-', [status(thm)], ['37', '38'])).
% 0.74/0.96  thf('40', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.74/0.96          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.74/0.96              != (sk_C @ k1_xboole_0 @ X0))
% 0.74/0.96          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.74/0.96          | ~ (l1_pre_topc @ X0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['36', '39'])).
% 0.74/0.96  thf('41', plain,
% 0.74/0.96      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf(redefinition_k9_subset_1, axiom,
% 0.74/0.96    (![A:$i,B:$i,C:$i]:
% 0.74/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.96       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.74/0.96  thf('42', plain,
% 0.74/0.96      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.74/0.96         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.74/0.96          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.74/0.96      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.74/0.96  thf('43', plain,
% 0.74/0.96      (![X0 : $i, X1 : $i]:
% 0.74/0.96         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.74/0.96           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['41', '42'])).
% 0.74/0.96  thf(t17_xboole_1, axiom,
% 0.74/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.96  thf('44', plain,
% 0.74/0.96      (![X1 : $i, X2 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X2) @ X1)),
% 0.74/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.74/0.96  thf('45', plain,
% 0.74/0.96      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.74/0.96  thf('46', plain,
% 0.74/0.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['44', '45'])).
% 0.74/0.96  thf('47', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.74/0.96          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.74/0.96          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.74/0.96          | ~ (l1_pre_topc @ X0))),
% 0.74/0.96      inference('demod', [status(thm)], ['40', '43', '46'])).
% 0.74/0.96  thf('48', plain,
% 0.74/0.96      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.74/0.96        | ~ (l1_pre_topc @ sk_A_1)
% 0.74/0.96        | (v2_tex_2 @ k1_xboole_0 @ sk_A_1)
% 0.74/0.96        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A_1)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['35', '47'])).
% 0.74/0.96  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.96      inference('demod', [status(thm)], ['28', '29'])).
% 0.74/0.96  thf('50', plain, ((l1_pre_topc @ sk_A_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('51', plain,
% 0.74/0.96      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.74/0.96      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.74/0.96  thf('52', plain,
% 0.74/0.96      (![X20 : $i, X21 : $i]:
% 0.74/0.96         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.74/0.96          | (r1_tarski @ (sk_C @ X20 @ X21) @ X20)
% 0.74/0.96          | (v2_tex_2 @ X20 @ X21)
% 0.74/0.96          | ~ (l1_pre_topc @ X21))),
% 0.74/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.74/0.96  thf('53', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         (~ (l1_pre_topc @ X0)
% 0.74/0.96          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.74/0.96          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['51', '52'])).
% 0.74/0.96  thf('54', plain,
% 0.74/0.96      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.74/0.96      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.74/0.96  thf('55', plain,
% 0.74/0.96      (![X0 : $i]:
% 0.74/0.96         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.74/0.96          | ~ (l1_pre_topc @ X0)
% 0.74/0.96          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.74/0.96      inference('sup-', [status(thm)], ['53', '54'])).
% 0.74/0.96  thf('56', plain,
% 0.74/0.96      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.74/0.96  thf('57', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A_1)),
% 0.74/0.96      inference('demod', [status(thm)], ['0', '3'])).
% 0.74/0.96  thf('58', plain,
% 0.74/0.96      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A_1) | ~ (v1_xboole_0 @ X0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['56', '57'])).
% 0.74/0.96  thf('59', plain,
% 0.74/0.96      ((((sk_C @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))
% 0.74/0.96        | ~ (l1_pre_topc @ sk_A_1)
% 0.74/0.96        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.74/0.96      inference('sup-', [status(thm)], ['55', '58'])).
% 0.74/0.96  thf('60', plain, ((l1_pre_topc @ sk_A_1)),
% 0.74/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.96  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.74/0.96      inference('demod', [status(thm)], ['28', '29'])).
% 0.74/0.96  thf('62', plain, (((sk_C @ k1_xboole_0 @ sk_A_1) = (k1_xboole_0))),
% 0.74/0.96      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.74/0.96  thf('63', plain,
% 0.74/0.96      (((v2_tex_2 @ k1_xboole_0 @ sk_A_1) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.74/0.96      inference('demod', [status(thm)], ['48', '49', '50', '62'])).
% 0.74/0.96  thf('64', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A_1)),
% 0.74/0.96      inference('simplify', [status(thm)], ['63'])).
% 0.74/0.96  thf('65', plain, ($false), inference('demod', [status(thm)], ['4', '64'])).
% 0.74/0.96  
% 0.74/0.96  % SZS output end Refutation
% 0.74/0.96  
% 0.74/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

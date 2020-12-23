%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qEJOk78zXi

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 115 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  628 (1104 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t26_tops_2,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
           => ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v1_tops_2 @ B @ A )
             => ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('2',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( r2_hidden @ X34 @ ( u1_pre_topc @ X35 ) )
      | ( v3_pre_topc @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A )
    | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) )
      | ~ ( v1_tops_2 @ X36 @ X37 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( v3_pre_topc @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( v1_tops_2 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tops_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X35 )
      | ( r2_hidden @ X34 @ ( u1_pre_topc @ X35 ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) )
      | ( r1_tarski @ sk_B_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_B_2 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['31'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf('33',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X25 @ ( u1_pre_topc @ X26 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ ( u1_pre_topc @ X26 ) )
      | ~ ( zip_tseitin_4 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,
    ( ~ ( zip_tseitin_4 @ sk_B_2 @ sk_A )
    | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X31: $i,X33: $i] :
      ( ~ ( v2_pre_topc @ X31 )
      | ( zip_tseitin_5 @ X33 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('36',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) )
      | ( zip_tseitin_4 @ X28 @ X29 )
      | ~ ( zip_tseitin_5 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,
    ( ~ ( zip_tseitin_5 @ sk_B_2 @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( zip_tseitin_4 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    zip_tseitin_4 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['34','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['8','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qEJOk78zXi
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:14:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 117 iterations in 0.073s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.20/0.52  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.20/0.52  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.20/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(t26_tops_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @
% 0.20/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ( v1_tops_2 @ B @ A ) =>
% 0.20/0.52             ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @
% 0.20/0.52                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52              ( ( v1_tops_2 @ B @ A ) =>
% 0.20/0.52                ( v3_pre_topc @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t26_tops_2])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_k5_setfam_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k5_setfam_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.20/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      ((m1_subset_1 @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.52  thf(d5_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.52             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.20/0.52          | ~ (r2_hidden @ X34 @ (u1_pre_topc @ X35))
% 0.20/0.52          | (v3_pre_topc @ X34 @ X35)
% 0.20/0.52          | ~ (l1_pre_topc @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.20/0.52        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.52             (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)
% 0.20/0.52        | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.52             (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (~ (v3_pre_topc @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.52          (u1_pre_topc @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d1_tops_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @
% 0.20/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52           ( ( v1_tops_2 @ B @ A ) <=>
% 0.20/0.52             ( ![C:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                 ( ( r2_hidden @ C @ B ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X36 @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37))))
% 0.20/0.52          | ~ (v1_tops_2 @ X36 @ X37)
% 0.20/0.52          | ~ (r2_hidden @ X38 @ X36)
% 0.20/0.52          | (v3_pre_topc @ X38 @ X37)
% 0.20/0.52          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 0.20/0.52          | ~ (l1_pre_topc @ X37))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_tops_2])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.20/0.52          | ~ (v1_tops_2 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('14', plain, ((v1_tops_2 @ sk_B_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v3_pre_topc @ X0 @ sk_A)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t4_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ X7)
% 0.20/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.20/0.52          | (m1_subset_1 @ X6 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_2) | (v3_pre_topc @ X0 @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['15', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B_2 @ X0)
% 0.20/0.52          | (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '19'])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B_2 @ X0)
% 0.20/0.52          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_2) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (![X34 : $i, X35 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.20/0.52          | ~ (v3_pre_topc @ X34 @ X35)
% 0.20/0.52          | (r2_hidden @ X34 @ (u1_pre_topc @ X35))
% 0.20/0.52          | ~ (l1_pre_topc @ X35))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B_2 @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B_2 @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          | ~ (v3_pre_topc @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B_2 @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          | (r1_tarski @ sk_B_2 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['20', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C @ X0 @ sk_B_2) @ (u1_pre_topc @ sk_A))
% 0.20/0.52          | (r1_tarski @ sk_B_2 @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))
% 0.20/0.52        | (r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.52  thf('32', plain, ((r1_tarski @ sk_B_2 @ (u1_pre_topc @ sk_A))),
% 0.20/0.52      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.52  thf(d1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.52         ( ( ![B:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ![C:$i]:
% 0.20/0.52                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.52                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.52                     ( r2_hidden @
% 0.20/0.52                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.20/0.52                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.20/0.52           ( ![B:$i]:
% 0.20/0.52             ( ( m1_subset_1 @
% 0.20/0.52                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.52                 ( r2_hidden @
% 0.20/0.52                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.52                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.20/0.52           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_1, axiom,
% 0.20/0.52    (![B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.20/0.52       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.52         ( r2_hidden @
% 0.20/0.52           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X25 : $i, X26 : $i]:
% 0.20/0.52         (~ (r1_tarski @ X25 @ (u1_pre_topc @ X26))
% 0.20/0.52          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X26) @ X25) @ 
% 0.20/0.52             (u1_pre_topc @ X26))
% 0.20/0.52          | ~ (zip_tseitin_4 @ X25 @ X26))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      ((~ (zip_tseitin_4 @ sk_B_2 @ sk_A)
% 0.20/0.52        | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.52           (u1_pre_topc @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_3, axiom,
% 0.20/0.52    (![B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.20/0.52       ( ( m1_subset_1 @
% 0.20/0.52           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.20/0.52  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_6, axiom,
% 0.20/0.52    (![B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.20/0.52       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_8, axiom,
% 0.20/0.52    (![C:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.20/0.52       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.20/0.52  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_10, axiom,
% 0.20/0.52    (![C:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.20/0.52       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.52         ( r2_hidden @
% 0.20/0.52           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.52  thf(zf_stmt_12, axiom,
% 0.20/0.52    (![C:$i,B:$i,A:$i]:
% 0.20/0.52     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.20/0.52       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.52         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_13, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ( v2_pre_topc @ A ) <=>
% 0.20/0.52         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.52           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.20/0.52           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X31 : $i, X33 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ X31)
% 0.20/0.52          | (zip_tseitin_5 @ X33 @ X31)
% 0.20/0.52          | ~ (l1_pre_topc @ X31))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B_2 @ 
% 0.20/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X28 @ 
% 0.20/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))
% 0.20/0.52          | (zip_tseitin_4 @ X28 @ X29)
% 0.20/0.52          | ~ (zip_tseitin_5 @ X28 @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((~ (zip_tseitin_5 @ sk_B_2 @ sk_A) | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | (zip_tseitin_4 @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.52  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain, ((zip_tseitin_4 @ sk_B_2 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.52        (u1_pre_topc @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['34', '42'])).
% 0.20/0.52  thf('44', plain, ($false), inference('demod', [status(thm)], ['8', '43'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

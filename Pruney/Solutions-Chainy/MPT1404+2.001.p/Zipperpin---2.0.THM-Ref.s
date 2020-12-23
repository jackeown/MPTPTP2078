%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wAzlxRW2lu

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 354 expanded)
%              Number of leaves         :   25 ( 105 expanded)
%              Depth                    :   20
%              Number of atoms          : 1855 (6199 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t34_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_connsp_2 @ D @ A @ C )
                   => ~ ( r1_xboole_0 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
                <=> ! [D: $i] :
                      ( ( m1_connsp_2 @ D @ A @ C )
                     => ~ ( r1_xboole_0 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_connsp_2])).

thf('0',plain,
    ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
      | ~ ( r1_xboole_0 @ X19 @ sk_B )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('7',plain,
    ( ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_connsp_2 @ X11 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_C )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r2_hidden @ X15 @ ( sk_D_1 @ X17 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( r2_hidden @ sk_C @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ sk_C @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( v3_pre_topc @ ( sk_D_1 @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_A )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_A )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_A )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
   <= ( r1_xboole_0 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,
    ( ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( r1_tarski @ ( sk_D_1 @ X17 @ X15 @ X16 ) @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r1_tarski @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ sk_D_2 )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( r1_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_D_2 )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['49','50'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( r1_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ X0 )
        | ~ ( r1_xboole_0 @ sk_D_2 @ X0 ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r1_xboole_0 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_B )
   <= ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
      & ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','53'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('56',plain,
    ( ( r1_xboole_0 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
   <= ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
      & ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_connsp_2 @ X17 @ X16 @ X15 )
      | ( m1_subset_1 @ ( sk_D_1 @ X17 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ( ~ ( v2_struct_0 @ A )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ~ ( ( v3_pre_topc @ D @ A )
                          & ( r2_hidden @ C @ D )
                          & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r2_hidden @ X7 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v3_pre_topc @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( r1_xboole_0 @ sk_B @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
        | ~ ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v3_pre_topc @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
      & ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_D_2 @ sk_C @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
      & ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','75'])).

thf('77',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
      & ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( r1_xboole_0 @ sk_D_2 @ sk_B )
      & ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( r1_xboole_0 @ sk_D_2 @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','79'])).

thf('81',plain,
    ( ! [X19: $i] :
        ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X19 @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v2_struct_0 @ X6 )
      | ( r1_xboole_0 @ X5 @ ( sk_D @ X7 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('92',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v2_struct_0 @ X6 )
      | ( r2_hidden @ X7 @ ( sk_D @ X7 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v2_struct_0 @ X6 )
      | ( v3_pre_topc @ ( sk_D @ X7 @ X5 @ X6 ) @ X6 )
      | ( r2_hidden @ X7 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['102','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v2_struct_0 @ X6 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r2_hidden @ X7 @ ( k2_pre_topc @ X6 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['117','118'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('120',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X12 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( m1_connsp_2 @ X12 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_connsp_2 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,
    ( ! [X19: $i] :
        ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X19 @ sk_B ) )
   <= ! [X19: $i] :
        ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X19 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('134',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ! [X19: $i] :
        ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X19: $i] :
        ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X19 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['92','134'])).

thf('136',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ! [X19: $i] :
        ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
        | ~ ( r1_xboole_0 @ X19 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('138',plain,
    ( ~ ! [X19: $i] :
          ( ~ ( m1_connsp_2 @ X19 @ sk_A @ sk_C )
          | ~ ( r1_xboole_0 @ X19 @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','80','81','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wAzlxRW2lu
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 149 iterations in 0.109s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.56  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.56  thf(t34_connsp_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.56                 ( ![D:$i]:
% 0.20/0.56                   ( ( m1_connsp_2 @ D @ A @ C ) =>
% 0.20/0.56                     ( ~( r1_xboole_0 @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56            ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ![C:$i]:
% 0.20/0.56                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56                  ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.56                    ( ![D:$i]:
% 0.20/0.56                      ( ( m1_connsp_2 @ D @ A @ C ) =>
% 0.20/0.56                        ( ~( r1_xboole_0 @ D @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t34_connsp_2])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      (((r1_xboole_0 @ sk_D_2 @ sk_B)
% 0.20/0.56        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (((r1_xboole_0 @ sk_D_2 @ sk_B)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)
% 0.20/0.56        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (![X19 : $i]:
% 0.20/0.56         (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C)
% 0.20/0.56          | ~ (r1_xboole_0 @ X19 @ sk_B)
% 0.20/0.56          | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.56         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('8', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_m1_connsp_2, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.56         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56       ( ![C:$i]:
% 0.20/0.56         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.20/0.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X9)
% 0.20/0.56          | ~ (v2_pre_topc @ X9)
% 0.20/0.56          | (v2_struct_0 @ X9)
% 0.20/0.56          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.56          | (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.56          | ~ (m1_connsp_2 @ X11 @ X9 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_C)
% 0.20/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.56  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_C))),
% 0.20/0.56      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '15'])).
% 0.20/0.56  thf(t8_connsp_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.56                 ( ?[D:$i]:
% 0.20/0.56                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.20/0.56                     ( v3_pre_topc @ D @ A ) & 
% 0.20/0.56                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.56          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.20/0.56          | (r2_hidden @ X15 @ (sk_D_1 @ X17 @ X15 @ X16))
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.56          | ~ (l1_pre_topc @ X16)
% 0.20/0.56          | ~ (v2_pre_topc @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56           | (r2_hidden @ X0 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A))
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.56  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | (r2_hidden @ X0 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A))
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (r2_hidden @ sk_C @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A))
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '21'])).
% 0.20/0.56  thf('23', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      ((((r2_hidden @ sk_C @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A))
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.56  thf('25', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A)))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '15'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.56          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.20/0.56          | (v3_pre_topc @ (sk_D_1 @ X17 @ X15 @ X16) @ X16)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.56          | ~ (l1_pre_topc @ X16)
% 0.20/0.56          | ~ (v2_pre_topc @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56           | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_A)
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_A)
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '33'])).
% 0.20/0.56  thf('35', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((((v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_A)
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      (((v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_A))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (((r1_xboole_0 @ sk_D_2 @ sk_B)) <= (((r1_xboole_0 @ sk_D_2 @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '15'])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.56          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.20/0.56          | (r1_tarski @ (sk_D_1 @ X17 @ X15 @ X16) @ X17)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.56          | ~ (l1_pre_topc @ X16)
% 0.20/0.56          | ~ (v2_pre_topc @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56           | (r1_tarski @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2)
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.56  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | (r1_tarski @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ sk_D_2)
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (r1_tarski @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '46'])).
% 0.20/0.56  thf('48', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      ((((r1_tarski @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2)
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (((r1_tarski @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_D_2))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf(t63_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.56       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (~ (r1_tarski @ X2 @ X3)
% 0.20/0.56          | ~ (r1_xboole_0 @ X3 @ X4)
% 0.20/0.56          | (r1_xboole_0 @ X2 @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.56  thf('53', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((r1_xboole_0 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ X0)
% 0.20/0.56           | ~ (r1_xboole_0 @ sk_D_2 @ X0)))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (((r1_xboole_0 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_B))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_D_2 @ sk_B)) & 
% 0.20/0.56             ((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['39', '53'])).
% 0.20/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.56  thf('55', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      (((r1_xboole_0 @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A)))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_D_2 @ sk_B)) & 
% 0.20/0.56             ((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('split', [status(esa)], ['2'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '15'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 0.20/0.56          | ~ (m1_connsp_2 @ X17 @ X16 @ X15)
% 0.20/0.56          | (m1_subset_1 @ (sk_D_1 @ X17 @ X15 @ X16) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.56          | ~ (l1_pre_topc @ X16)
% 0.20/0.56          | ~ (v2_pre_topc @ X16)
% 0.20/0.56          | (v2_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t8_connsp_2])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56           | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ 
% 0.20/0.56              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          ((v2_struct_0 @ sk_A)
% 0.20/0.56           | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ X0 @ sk_A) @ 
% 0.20/0.56              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56           | ~ (m1_connsp_2 @ sk_D_2 @ sk_A @ X0)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ 
% 0.20/0.56            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['57', '63'])).
% 0.20/0.56  thf('65', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('66', plain,
% 0.20/0.56      ((((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ 
% 0.20/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['64', '65'])).
% 0.20/0.56  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('68', plain,
% 0.20/0.56      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ 
% 0.20/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t54_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.56                 ( ( ~( v2_struct_0 @ A ) ) & 
% 0.20/0.56                   ( ![D:$i]:
% 0.20/0.56                     ( ( m1_subset_1 @
% 0.20/0.56                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 0.20/0.56                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('70', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | ~ (r2_hidden @ X7 @ (k2_pre_topc @ X6 @ X5))
% 0.20/0.56          | ~ (r1_xboole_0 @ X5 @ X8)
% 0.20/0.56          | ~ (r2_hidden @ X7 @ X8)
% 0.20/0.56          | ~ (v3_pre_topc @ X8 @ X6)
% 0.20/0.56          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.56          | ~ (r1_xboole_0 @ sk_B @ X1)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.56  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.56          | ~ (r1_xboole_0 @ sk_B @ X1)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.56  thf('74', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56           | ~ (r1_xboole_0 @ sk_B @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A))
% 0.20/0.56           | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A))
% 0.20/0.56           | ~ (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_A)
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['68', '73'])).
% 0.20/0.56  thf('75', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56           | ~ (v3_pre_topc @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A) @ sk_A)
% 0.20/0.56           | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A))
% 0.20/0.56           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_D_2 @ sk_B)) & 
% 0.20/0.56             ((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['56', '74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      ((![X0 : $i]:
% 0.20/0.56          (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56           | ~ (r2_hidden @ X0 @ (sk_D_1 @ sk_D_2 @ sk_C @ sk_A))
% 0.20/0.56           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_D_2 @ sk_B)) & 
% 0.20/0.56             ((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '75'])).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.56         | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_D_2 @ sk_B)) & 
% 0.20/0.56             ((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '76'])).
% 0.20/0.56  thf('78', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('79', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.56         <= (((r1_xboole_0 @ sk_D_2 @ sk_B)) & 
% 0.20/0.56             ((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)))),
% 0.20/0.56      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      (~ ((r1_xboole_0 @ sk_D_2 @ sk_B)) | 
% 0.20/0.56       ~ ((m1_connsp_2 @ sk_D_2 @ sk_A @ sk_C)) | 
% 0.20/0.56       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '79'])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      ((![X19 : $i]:
% 0.20/0.56          (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C) | ~ (r1_xboole_0 @ X19 @ sk_B))) | 
% 0.20/0.56       ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('82', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('84', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | (v2_struct_0 @ X6)
% 0.20/0.56          | (r1_xboole_0 @ X5 @ (sk_D @ X7 @ X5 @ X6))
% 0.20/0.56          | (r2_hidden @ X7 @ (k2_pre_topc @ X6 @ X5))
% 0.20/0.56          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (r1_xboole_0 @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['83', '84'])).
% 0.20/0.56  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('87', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (r1_xboole_0 @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.56  thf('88', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (r1_xboole_0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['82', '87'])).
% 0.20/0.56  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('90', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (r1_xboole_0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['88', '89'])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.56  thf('92', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (r1_xboole_0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.56  thf('93', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('94', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('95', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | (v2_struct_0 @ X6)
% 0.20/0.56          | (r2_hidden @ X7 @ (sk_D @ X7 @ X5 @ X6))
% 0.20/0.56          | (r2_hidden @ X7 @ (k2_pre_topc @ X6 @ X5))
% 0.20/0.56          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.56  thf('96', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.56  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('98', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['96', '97'])).
% 0.20/0.56  thf('99', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['93', '98'])).
% 0.20/0.56  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('101', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.56      inference('clc', [status(thm)], ['99', '100'])).
% 0.20/0.56  thf('102', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('103', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('104', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | (v2_struct_0 @ X6)
% 0.20/0.56          | (v3_pre_topc @ (sk_D @ X7 @ X5 @ X6) @ X6)
% 0.20/0.56          | (r2_hidden @ X7 @ (k2_pre_topc @ X6 @ X5))
% 0.20/0.56          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.56  thf('105', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.56  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('107', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.56  thf('108', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['102', '107'])).
% 0.20/0.56  thf('109', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('110', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.56      inference('clc', [status(thm)], ['108', '109'])).
% 0.20/0.56  thf('111', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('112', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('113', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | (v2_struct_0 @ X6)
% 0.20/0.56          | (m1_subset_1 @ (sk_D @ X7 @ X5 @ X6) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.20/0.56          | (r2_hidden @ X7 @ (k2_pre_topc @ X6 @ X5))
% 0.20/0.56          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 0.20/0.56          | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.56  thf('114', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['112', '113'])).
% 0.20/0.56  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('116', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['114', '115'])).
% 0.20/0.56  thf('117', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['111', '116'])).
% 0.20/0.56  thf('118', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('119', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('clc', [status(thm)], ['117', '118'])).
% 0.20/0.56  thf(t5_connsp_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.20/0.56                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.20/0.56  thf('120', plain,
% 0.20/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.56          | ~ (v3_pre_topc @ X12 @ X13)
% 0.20/0.56          | ~ (r2_hidden @ X14 @ X12)
% 0.20/0.56          | (m1_connsp_2 @ X12 @ X13 @ X14)
% 0.20/0.56          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.20/0.56          | ~ (l1_pre_topc @ X13)
% 0.20/0.56          | ~ (v2_pre_topc @ X13)
% 0.20/0.56          | (v2_struct_0 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.20/0.56  thf('121', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.56          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.56          | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['119', '120'])).
% 0.20/0.56  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('124', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.56          | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['121', '122', '123'])).
% 0.20/0.56  thf('125', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.56          | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (v2_struct_0 @ sk_A)
% 0.20/0.56          | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['110', '124'])).
% 0.20/0.56  thf('126', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_struct_0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.56          | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ X0)
% 0.20/0.56          | ~ (r2_hidden @ X0 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.56          | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['125'])).
% 0.20/0.56  thf('127', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C)
% 0.20/0.56        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['101', '126'])).
% 0.20/0.56  thf('128', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('129', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C)
% 0.20/0.56        | (v2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['127', '128'])).
% 0.20/0.56  thf('130', plain,
% 0.20/0.56      (((v2_struct_0 @ sk_A)
% 0.20/0.56        | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C)
% 0.20/0.56        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('simplify', [status(thm)], ['129'])).
% 0.20/0.56  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('132', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (m1_connsp_2 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A @ sk_C))),
% 0.20/0.56      inference('clc', [status(thm)], ['130', '131'])).
% 0.20/0.56  thf('133', plain,
% 0.20/0.56      ((![X19 : $i]:
% 0.20/0.56          (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C) | ~ (r1_xboole_0 @ X19 @ sk_B)))
% 0.20/0.56         <= ((![X19 : $i]:
% 0.20/0.56                (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C)
% 0.20/0.56                 | ~ (r1_xboole_0 @ X19 @ sk_B))))),
% 0.20/0.56      inference('split', [status(esa)], ['4'])).
% 0.20/0.56  thf('134', plain,
% 0.20/0.56      ((((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56         | ~ (r1_xboole_0 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)))
% 0.20/0.56         <= ((![X19 : $i]:
% 0.20/0.56                (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C)
% 0.20/0.56                 | ~ (r1_xboole_0 @ X19 @ sk_B))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['132', '133'])).
% 0.20/0.56  thf('135', plain,
% 0.20/0.56      ((((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.56         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.56         <= ((![X19 : $i]:
% 0.20/0.56                (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C)
% 0.20/0.56                 | ~ (r1_xboole_0 @ X19 @ sk_B))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['92', '134'])).
% 0.20/0.56  thf('136', plain,
% 0.20/0.56      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.56         <= ((![X19 : $i]:
% 0.20/0.56                (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C)
% 0.20/0.56                 | ~ (r1_xboole_0 @ X19 @ sk_B))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['135'])).
% 0.20/0.56  thf('137', plain,
% 0.20/0.56      ((~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.56         <= (~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.56      inference('split', [status(esa)], ['0'])).
% 0.20/0.56  thf('138', plain,
% 0.20/0.56      (~
% 0.20/0.56       (![X19 : $i]:
% 0.20/0.56          (~ (m1_connsp_2 @ X19 @ sk_A @ sk_C) | ~ (r1_xboole_0 @ X19 @ sk_B))) | 
% 0.20/0.56       ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['136', '137'])).
% 0.20/0.56  thf('139', plain, ($false),
% 0.20/0.56      inference('sat_resolution*', [status(thm)], ['1', '3', '80', '81', '138'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

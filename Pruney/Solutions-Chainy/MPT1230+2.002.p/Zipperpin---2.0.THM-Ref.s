%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tIKRlW0vKM

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 161 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          : 1067 (3315 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t39_tops_1,conjecture,(
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
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ~ ( ( v3_pre_topc @ D @ A )
                        & ( r2_hidden @ C @ D )
                        & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) )).

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
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ~ ( ( v3_pre_topc @ D @ A )
                          & ( r2_hidden @ C @ D )
                          & ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_tops_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X4: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X4 @ sk_A )
      | ~ ( r2_hidden @ sk_C @ X4 )
      | ~ ( r1_xboole_0 @ sk_B @ X4 )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ( r1_xboole_0 @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_xboole_0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r1_xboole_0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_D @ X2 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) )
   <= ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('27',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ( r2_hidden @ X2 @ ( sk_D @ X2 @ X0 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) ) ),
    inference(clc,[status(thm)],['29','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v2_struct_0 @ X1 )
      | ( v3_pre_topc @ ( sk_D @ X2 @ X0 @ X1 ) @ X1 )
      | ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( v3_pre_topc @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ! [X4: $i] :
        ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X4 @ sk_A )
        | ~ ( r2_hidden @ sk_C @ X4 )
        | ~ ( r1_xboole_0 @ sk_B @ X4 ) ) ),
    inference(clc,[status(thm)],['39','48'])).

thf('50',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ~ ! [X4: $i] :
          ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X4 @ sk_A )
          | ~ ( r2_hidden @ sk_C @ X4 )
          | ~ ( r1_xboole_0 @ sk_B @ X4 ) )
    | ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['50'])).

thf('54',plain,
    ( ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( r2_hidden @ sk_C @ sk_D_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,
    ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['6'])).

thf('56',plain,
    ( ( v3_pre_topc @ sk_D_1 @ sk_A )
   <= ( v3_pre_topc @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('57',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['50'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_pre_topc @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v3_pre_topc @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t54_pre_topc])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( r1_xboole_0 @ sk_B @ sk_D_1 )
        | ~ ( r2_hidden @ X0 @ sk_D_1 )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_D_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_D_1 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C @ sk_D_1 ) )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_D_1 )
   <= ( ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
      & ( r1_xboole_0 @ sk_B @ sk_D_1 )
      & ( v3_pre_topc @ sk_D_1 @ sk_A )
      & ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_D_1 )
    | ~ ( r2_hidden @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_D_1 @ sk_A )
    | ~ ( r2_hidden @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','52','53','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tIKRlW0vKM
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:04:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 89 iterations in 0.074s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(t39_tops_1, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.52                 ( ![D:$i]:
% 0.20/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                     ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 0.20/0.52                          ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52                  ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.52                    ( ![D:$i]:
% 0.20/0.52                      ( ( m1_subset_1 @
% 0.20/0.52                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                        ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 0.20/0.52                             ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t39_tops_1])).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (((r2_hidden @ sk_C @ sk_D_1)
% 0.20/0.52        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (((r2_hidden @ sk_C @ sk_D_1)) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['0'])).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_D_1 @ sk_A)
% 0.20/0.52        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((v3_pre_topc @ sk_D_1 @ sk_A)) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['2'])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.52       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X4 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52          | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52          | ~ (r1_xboole_0 @ sk_B @ X4)
% 0.20/0.52          | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((![X4 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52           | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52           | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52           | ~ (r1_xboole_0 @ sk_B @ X4))) | 
% 0.20/0.52       ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('8', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t54_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.20/0.52                 ( ( ~( v2_struct_0 @ A ) ) & 
% 0.20/0.52                   ( ![D:$i]:
% 0.20/0.52                     ( ( m1_subset_1 @
% 0.20/0.52                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                       ( ~( ( v3_pre_topc @ D @ A ) & ( r2_hidden @ C @ D ) & 
% 0.20/0.52                            ( r1_xboole_0 @ B @ D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (r1_xboole_0 @ X0 @ (sk_D @ X2 @ X0 @ X1))
% 0.20/0.52          | (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.52          | ~ (l1_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (r1_xboole_0 @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (r1_xboole_0 @ sk_B @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (r1_xboole_0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.52  thf('15', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52        | (r1_xboole_0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (m1_subset_1 @ (sk_D @ X2 @ X0 @ X1) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.52          | (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.52          | ~ (l1_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.52  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((![X4 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52           | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52           | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52           | ~ (r1_xboole_0 @ sk_B @ X4)))
% 0.20/0.52         <= ((![X4 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52                 | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52                 | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52                 | ~ (r1_xboole_0 @ sk_B @ X4))))),
% 0.20/0.52      inference('split', [status(esa)], ['6'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      ((((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52         | ~ (r1_xboole_0 @ sk_B @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52         | ~ (r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52         | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.20/0.52         <= ((![X4 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52                 | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52                 | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52                 | ~ (r1_xboole_0 @ sk_B @ X4))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52         | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.52         | ~ (r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.52         <= ((![X4 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52                 | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52                 | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52                 | ~ (r1_xboole_0 @ sk_B @ X4))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['16', '27'])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (((~ (r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52         | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.52         | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.52         <= ((![X4 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52                 | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52                 | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52                 | ~ (r1_xboole_0 @ sk_B @ X4))))),
% 0.20/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.52  thf('30', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (r2_hidden @ X2 @ (sk_D @ X2 @ X0 @ X1))
% 0.20/0.52          | (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.52          | ~ (l1_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.52  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (r2_hidden @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.20/0.52        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.52  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52        | (r2_hidden @ sk_C @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52         | ~ (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)))
% 0.20/0.52         <= ((![X4 : $i]:
% 0.20/0.52                (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52                 | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.52                 | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.52                 | ~ (r1_xboole_0 @ sk_B @ X4))))),
% 0.20/0.52      inference('clc', [status(thm)], ['29', '38'])).
% 0.20/0.52  thf('40', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.52          | (v2_struct_0 @ X1)
% 0.20/0.52          | (v3_pre_topc @ (sk_D @ X2 @ X0 @ X1) @ X1)
% 0.20/0.52          | (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.20/0.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.52          | ~ (l1_pre_topc @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.52          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A)
% 0.20/0.52        | (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.53        | (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '45'])).
% 0.20/0.53  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.53        | (v3_pre_topc @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.53         <= ((![X4 : $i]:
% 0.20/0.53                (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53                 | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.53                 | ~ (r1_xboole_0 @ sk_B @ X4))))),
% 0.20/0.53      inference('clc', [status(thm)], ['39', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_B @ sk_D_1)
% 0.20/0.53        | ~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (~
% 0.20/0.53       (![X4 : $i]:
% 0.20/0.53          (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53           | ~ (v3_pre_topc @ X4 @ sk_A)
% 0.20/0.53           | ~ (r2_hidden @ sk_C @ X4)
% 0.20/0.53           | ~ (r1_xboole_0 @ sk_B @ X4))) | 
% 0.20/0.53       ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_B @ sk_D_1)) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['50'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ sk_D_1)) <= (((r2_hidden @ sk_C @ sk_D_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 0.20/0.53         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))),
% 0.20/0.53      inference('split', [status(esa)], ['6'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (((v3_pre_topc @ sk_D_1 @ sk_A)) <= (((v3_pre_topc @ sk_D_1 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['2'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_B @ sk_D_1)) <= (((r1_xboole_0 @ sk_B @ sk_D_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['50'])).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ~ (r2_hidden @ X2 @ (k2_pre_topc @ X1 @ X0))
% 0.20/0.53          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.20/0.53          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.53          | ~ (v3_pre_topc @ X3 @ X1)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.53          | ~ (l1_pre_topc @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [t54_pre_topc])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | ~ (r1_xboole_0 @ sk_B @ X1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (v3_pre_topc @ X1 @ sk_A)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | ~ (r1_xboole_0 @ sk_B @ X1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.53           | ~ (r1_xboole_0 @ sk_B @ sk_D_1)
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.20/0.53           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['58', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53           | ~ (v3_pre_topc @ sk_D_1 @ sk_A)
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.20/0.53           | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '64'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_D_1)
% 0.20/0.53           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['56', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (r2_hidden @ sk_C @ sk_D_1)))
% 0.20/0.53         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.53             ((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['55', '66'])).
% 0.20/0.53  thf('68', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_C @ sk_D_1))
% 0.20/0.53         <= (((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) & 
% 0.20/0.53             ((r1_xboole_0 @ sk_B @ sk_D_1)) & 
% 0.20/0.53             ((v3_pre_topc @ sk_D_1 @ sk_A)) & 
% 0.20/0.53             ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.53      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (~ ((r1_xboole_0 @ sk_B @ sk_D_1)) | 
% 0.20/0.53       ~ ((r2_hidden @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))) | 
% 0.20/0.53       ~ ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.53       ~ ((v3_pre_topc @ sk_D_1 @ sk_A)) | ~ ((r2_hidden @ sk_C @ sk_D_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['54', '69'])).
% 0.20/0.53  thf('71', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)],
% 0.20/0.53                ['1', '3', '5', '7', '52', '53', '70'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iKax0jI9jU

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:56 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 293 expanded)
%              Number of leaves         :   28 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          : 1446 (5135 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t8_connsp_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_connsp_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X34 @ sk_A )
      | ~ ( r1_tarski @ X34 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X34 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X34 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X9 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X34 ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X34 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('34',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X34 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['25','26'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( v2_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('38',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ! [X34: $i] :
        ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X34 @ sk_A )
        | ~ ( r1_tarski @ X34 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X34 ) ) ),
    inference(demod,[status(thm)],['34','35','41'])).

thf('43',plain,
    ( ~ ! [X34: $i] :
          ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X34 @ sk_A )
          | ~ ( r1_tarski @ X34 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X34 ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','42'])).

thf('44',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_B @ sk_D_2 )
   <= ( r2_hidden @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
   <= ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('48',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('49',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D_2 @ X0 )
        | ~ ( r1_tarski @ sk_C_1 @ X0 ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r1_tarski @ sk_D_2 @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

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

thf('55',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('56',plain,
    ( ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) )
   <= ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('59',plain,
    ( ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ~ ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ! [X13: $i,X14: $i] :
        ( ~ ( l1_pre_topc @ X13 )
        | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
        | ~ ( v3_pre_topc @ X14 @ X13 )
        | ( ( k1_tops_1 @ X13 @ X14 )
          = X14 ) )
    | ! [X15: $i,X16: $i] :
        ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( l1_pre_topc @ X16 )
        | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(split,[status(esa)],['58'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 ) ) ),
    inference('sat_resolution*',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ X14 @ X13 )
      | ( ( k1_tops_1 @ X13 @ X14 )
        = X14 ) ) ),
    inference(simpl_trail,[status(thm)],['56','65'])).

thf('67',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_D_2 )
        = sk_D_2 )
      | ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_D_2 )
        = sk_D_2 )
      | ~ ( v3_pre_topc @ sk_D_2 @ sk_A ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D_2 )
      = sk_D_2 )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('73',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ ( k1_tops_1 @ X11 @ X10 ) @ ( k1_tops_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D_2 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_2 @ X0 ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D_2 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D_2 @ X0 ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ~ ( r1_tarski @ sk_D_2 @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D_2 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('79',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D_2 ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_D_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','79'])).

thf('81',plain,
    ( ( v3_pre_topc @ sk_D_2 @ sk_A )
   <= ( v3_pre_topc @ sk_D_2 @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('82',plain,
    ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t57_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ B )
              <=> ? [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                    & ( v3_pre_topc @ D @ A )
                    & ( r1_tarski @ D @ B )
                    & ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ D )
        & ( r1_tarski @ D @ B )
        & ( v3_pre_topc @ D @ A )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('83',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X18 @ X17 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X21 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('84',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D_2 )
        | ~ ( r1_tarski @ sk_D_2 @ X1 )
        | ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
        | ( zip_tseitin_0 @ sk_D_2 @ X0 @ X1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ sk_D_2 @ X1 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_D_2 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_D_2 ) )
   <= ( ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D_2 )
        | ( zip_tseitin_0 @ sk_D_2 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ( ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,
    ( ( zip_tseitin_0 @ sk_D_2 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
   <= ( ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','86'])).

thf('88',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ B )
              <=> ? [D: $i] :
                    ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) )).

thf('89',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X23 )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( zip_tseitin_0 @ X25 @ X24 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_0 @ X1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D_2 )
      & ( r1_tarski @ sk_D_2 @ sk_C_1 )
      & ( v3_pre_topc @ sk_D_2 @ sk_A )
      & ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('108',plain,
    ( ~ ( v3_pre_topc @ sk_D_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D_2 @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_D_2 )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','43','45','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iKax0jI9jU
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:37:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 323 iterations in 0.093s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.57  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.57  thf(t8_connsp_2, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.57           ( ![C:$i]:
% 0.36/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.57                 ( ?[D:$i]:
% 0.36/0.57                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.36/0.57                     ( v3_pre_topc @ D @ A ) & 
% 0.36/0.57                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.57            ( l1_pre_topc @ A ) ) =>
% 0.36/0.57          ( ![B:$i]:
% 0.36/0.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.57              ( ![C:$i]:
% 0.36/0.57                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.57                    ( ?[D:$i]:
% 0.36/0.57                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.36/0.57                        ( v3_pre_topc @ D @ A ) & 
% 0.36/0.57                        ( m1_subset_1 @
% 0.36/0.57                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      (((r2_hidden @ sk_B @ sk_D_2) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      (((r2_hidden @ sk_B @ sk_D_2)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      (((r1_tarski @ sk_D_2 @ sk_C_1) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (((r1_tarski @ sk_D_2 @ sk_C_1)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('split', [status(esa)], ['2'])).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.36/0.57       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('split', [status(esa)], ['4'])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (![X34 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57          | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.36/0.57          | ~ (r1_tarski @ X34 @ sk_C_1)
% 0.36/0.57          | ~ (r2_hidden @ sk_B @ X34)
% 0.36/0.57          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      ((![X34 : $i]:
% 0.36/0.57          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57           | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.36/0.57           | ~ (r1_tarski @ X34 @ sk_C_1)
% 0.36/0.57           | ~ (r2_hidden @ sk_B @ X34))) | 
% 0.36/0.57       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('split', [status(esa)], ['6'])).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.57         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(d1_connsp_2, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.57           ( ![C:$i]:
% 0.36/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.57                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf('10', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.36/0.57          | ~ (m1_connsp_2 @ X30 @ X29 @ X28)
% 0.36/0.57          | (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 0.36/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.36/0.57          | ~ (l1_pre_topc @ X29)
% 0.36/0.57          | ~ (v2_pre_topc @ X29)
% 0.36/0.57          | (v2_struct_0 @ X29))),
% 0.36/0.57      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v2_struct_0 @ sk_A)
% 0.36/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.57          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.57  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('14', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v2_struct_0 @ sk_A)
% 0.36/0.57          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.57         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['8', '14'])).
% 0.36/0.57  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.36/0.57  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.57         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('clc', [status(thm)], ['17', '18'])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t3_subset, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (![X3 : $i, X4 : $i]:
% 0.36/0.57         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.57  thf('22', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t44_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      (![X8 : $i, X9 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.36/0.57          | (r1_tarski @ (k1_tops_1 @ X9 @ X8) @ X8)
% 0.36/0.57          | ~ (l1_pre_topc @ X9))),
% 0.36/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.57  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('27', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.36/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.57  thf(t1_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.57       ( r1_tarski @ A @ C ) ))).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.57          | ~ (r1_tarski @ X1 @ X2)
% 0.36/0.57          | (r1_tarski @ X0 @ X2))),
% 0.36/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.36/0.57          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['22', '29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (![X3 : $i, X5 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      ((![X34 : $i]:
% 0.36/0.57          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57           | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.36/0.57           | ~ (r1_tarski @ X34 @ sk_C_1)
% 0.36/0.57           | ~ (r2_hidden @ sk_B @ X34)))
% 0.36/0.57         <= ((![X34 : $i]:
% 0.36/0.57                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.36/0.57                 | ~ (r1_tarski @ X34 @ sk_C_1)
% 0.36/0.57                 | ~ (r2_hidden @ sk_B @ X34))))),
% 0.36/0.57      inference('split', [status(esa)], ['6'])).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.36/0.57         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.36/0.57         <= ((![X34 : $i]:
% 0.36/0.57                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.36/0.57                 | ~ (r1_tarski @ X34 @ sk_C_1)
% 0.36/0.57                 | ~ (r2_hidden @ sk_B @ X34))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.36/0.57  thf('35', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.36/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(fc9_tops_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.57       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X6)
% 0.36/0.57          | ~ (v2_pre_topc @ X6)
% 0.36/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.36/0.57          | (v3_pre_topc @ (k1_tops_1 @ X6 @ X7) @ X6))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.36/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.57  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('41', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.57  thf('42', plain,
% 0.36/0.57      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.57         <= ((![X34 : $i]:
% 0.36/0.57                (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57                 | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.36/0.57                 | ~ (r1_tarski @ X34 @ sk_C_1)
% 0.36/0.57                 | ~ (r2_hidden @ sk_B @ X34))))),
% 0.36/0.57      inference('demod', [status(thm)], ['34', '35', '41'])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (~
% 0.36/0.57       (![X34 : $i]:
% 0.36/0.57          (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57           | ~ (v3_pre_topc @ X34 @ sk_A)
% 0.36/0.57           | ~ (r1_tarski @ X34 @ sk_C_1)
% 0.36/0.57           | ~ (r2_hidden @ sk_B @ X34))) | 
% 0.36/0.57       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['19', '42'])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_D_2 @ sk_A) | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_D_2 @ sk_A)) | ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('split', [status(esa)], ['44'])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (((r2_hidden @ sk_B @ sk_D_2)) <= (((r2_hidden @ sk_B @ sk_D_2)))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_D_2 @ sk_A)) <= (((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['44'])).
% 0.36/0.57  thf('48', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      (((r1_tarski @ sk_D_2 @ sk_C_1)) <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('split', [status(esa)], ['2'])).
% 0.36/0.57  thf('50', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.57         (~ (r1_tarski @ X0 @ X1)
% 0.36/0.57          | ~ (r1_tarski @ X1 @ X2)
% 0.36/0.57          | (r1_tarski @ X0 @ X2))),
% 0.36/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.57  thf('51', plain,
% 0.36/0.57      ((![X0 : $i]: ((r1_tarski @ sk_D_2 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      (((r1_tarski @ sk_D_2 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['48', '51'])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (![X3 : $i, X5 : $i]:
% 0.36/0.57         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.36/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.57  thf(t55_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( l1_pre_topc @ B ) =>
% 0.36/0.57           ( ![C:$i]:
% 0.36/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57               ( ![D:$i]:
% 0.36/0.57                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.36/0.57                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.36/0.57                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.36/0.57                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.36/0.57                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X13)
% 0.36/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.57          | ~ (v3_pre_topc @ X14 @ X13)
% 0.36/0.57          | ((k1_tops_1 @ X13 @ X14) = (X14))
% 0.36/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.57          | ~ (l1_pre_topc @ X16)
% 0.36/0.57          | ~ (v2_pre_topc @ X16))),
% 0.36/0.57      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      ((![X13 : $i, X14 : $i]:
% 0.36/0.57          (~ (l1_pre_topc @ X13)
% 0.36/0.57           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.57           | ~ (v3_pre_topc @ X14 @ X13)
% 0.36/0.57           | ((k1_tops_1 @ X13 @ X14) = (X14))))
% 0.36/0.57         <= ((![X13 : $i, X14 : $i]:
% 0.36/0.57                (~ (l1_pre_topc @ X13)
% 0.36/0.57                 | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.57                 | ~ (v3_pre_topc @ X14 @ X13)
% 0.36/0.57                 | ((k1_tops_1 @ X13 @ X14) = (X14)))))),
% 0.36/0.57      inference('split', [status(esa)], ['55'])).
% 0.36/0.57  thf('57', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X13)
% 0.36/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.57          | ~ (v3_pre_topc @ X14 @ X13)
% 0.36/0.57          | ((k1_tops_1 @ X13 @ X14) = (X14))
% 0.36/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.57          | ~ (l1_pre_topc @ X16)
% 0.36/0.57          | ~ (v2_pre_topc @ X16))),
% 0.36/0.57      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.36/0.57  thf('59', plain,
% 0.36/0.57      ((![X15 : $i, X16 : $i]:
% 0.36/0.57          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.57           | ~ (l1_pre_topc @ X16)
% 0.36/0.57           | ~ (v2_pre_topc @ X16)))
% 0.36/0.57         <= ((![X15 : $i, X16 : $i]:
% 0.36/0.57                (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.57                 | ~ (l1_pre_topc @ X16)
% 0.36/0.57                 | ~ (v2_pre_topc @ X16))))),
% 0.36/0.57      inference('split', [status(esa)], ['58'])).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.36/0.57         <= ((![X15 : $i, X16 : $i]:
% 0.36/0.57                (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.57                 | ~ (l1_pre_topc @ X16)
% 0.36/0.57                 | ~ (v2_pre_topc @ X16))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['57', '59'])).
% 0.36/0.57  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      (~
% 0.36/0.57       (![X15 : $i, X16 : $i]:
% 0.36/0.57          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.57           | ~ (l1_pre_topc @ X16)
% 0.36/0.57           | ~ (v2_pre_topc @ X16)))),
% 0.36/0.57      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      ((![X13 : $i, X14 : $i]:
% 0.36/0.57          (~ (l1_pre_topc @ X13)
% 0.36/0.57           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.57           | ~ (v3_pre_topc @ X14 @ X13)
% 0.36/0.57           | ((k1_tops_1 @ X13 @ X14) = (X14)))) | 
% 0.36/0.57       (![X15 : $i, X16 : $i]:
% 0.36/0.57          (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.57           | ~ (l1_pre_topc @ X16)
% 0.36/0.57           | ~ (v2_pre_topc @ X16)))),
% 0.36/0.57      inference('split', [status(esa)], ['58'])).
% 0.36/0.57  thf('65', plain,
% 0.36/0.57      ((![X13 : $i, X14 : $i]:
% 0.36/0.57          (~ (l1_pre_topc @ X13)
% 0.36/0.57           | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.57           | ~ (v3_pre_topc @ X14 @ X13)
% 0.36/0.57           | ((k1_tops_1 @ X13 @ X14) = (X14))))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['63', '64'])).
% 0.36/0.57  thf('66', plain,
% 0.36/0.57      (![X13 : $i, X14 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X13)
% 0.36/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.36/0.57          | ~ (v3_pre_topc @ X14 @ X13)
% 0.36/0.57          | ((k1_tops_1 @ X13 @ X14) = (X14)))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['56', '65'])).
% 0.36/0.57  thf('67', plain,
% 0.36/0.57      (((((k1_tops_1 @ sk_A @ sk_D_2) = (sk_D_2))
% 0.36/0.57         | ~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 0.36/0.57         | ~ (l1_pre_topc @ sk_A))) <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['54', '66'])).
% 0.36/0.57  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('69', plain,
% 0.36/0.57      (((((k1_tops_1 @ sk_A @ sk_D_2) = (sk_D_2))
% 0.36/0.57         | ~ (v3_pre_topc @ sk_D_2 @ sk_A)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.36/0.57  thf('70', plain,
% 0.36/0.57      ((((k1_tops_1 @ sk_A @ sk_D_2) = (sk_D_2)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['47', '69'])).
% 0.36/0.57  thf('71', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('72', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.57  thf(t48_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ![C:$i]:
% 0.36/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57               ( ( r1_tarski @ B @ C ) =>
% 0.36/0.57                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf('73', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.36/0.57          | ~ (r1_tarski @ X10 @ X12)
% 0.36/0.57          | (r1_tarski @ (k1_tops_1 @ X11 @ X10) @ (k1_tops_1 @ X11 @ X12))
% 0.36/0.57          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.36/0.57          | ~ (l1_pre_topc @ X11))),
% 0.36/0.57      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.36/0.57  thf('74', plain,
% 0.36/0.57      ((![X0 : $i]:
% 0.36/0.57          (~ (l1_pre_topc @ sk_A)
% 0.36/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D_2) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.57           | ~ (r1_tarski @ sk_D_2 @ X0)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.36/0.57  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('76', plain,
% 0.36/0.57      ((![X0 : $i]:
% 0.36/0.57          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D_2) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.57           | ~ (r1_tarski @ sk_D_2 @ X0)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('demod', [status(thm)], ['74', '75'])).
% 0.36/0.57  thf('77', plain,
% 0.36/0.57      (((~ (r1_tarski @ sk_D_2 @ sk_C_1)
% 0.36/0.57         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D_2) @ 
% 0.36/0.57            (k1_tops_1 @ sk_A @ sk_C_1))))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['71', '76'])).
% 0.36/0.57  thf('78', plain,
% 0.36/0.57      (((r1_tarski @ sk_D_2 @ sk_C_1)) <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('split', [status(esa)], ['2'])).
% 0.36/0.57  thf('79', plain,
% 0.36/0.57      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D_2) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)))),
% 0.36/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.57  thf('80', plain,
% 0.36/0.57      (((r1_tarski @ sk_D_2 @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & ((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['70', '79'])).
% 0.36/0.57  thf('81', plain,
% 0.36/0.57      (((v3_pre_topc @ sk_D_2 @ sk_A)) <= (((v3_pre_topc @ sk_D_2 @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['44'])).
% 0.36/0.57  thf('82', plain,
% 0.36/0.57      (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.36/0.57         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('split', [status(esa)], ['4'])).
% 0.36/0.57  thf(t57_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( l1_pre_topc @ A ) & ( v2_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.36/0.57             ( ![C:$i]:
% 0.36/0.57               ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.57                 ( ?[D:$i]:
% 0.36/0.57                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.36/0.57                     ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ B ) & 
% 0.36/0.57                     ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_1, axiom,
% 0.36/0.57    (![D:$i,C:$i,B:$i,A:$i]:
% 0.36/0.57     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.36/0.57       ( ( r2_hidden @ C @ D ) & ( r1_tarski @ D @ B ) & 
% 0.36/0.57         ( v3_pre_topc @ D @ A ) & 
% 0.36/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.36/0.57  thf('83', plain,
% 0.36/0.57      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.36/0.57         ((zip_tseitin_0 @ X18 @ X17 @ X19 @ X21)
% 0.36/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.36/0.57          | ~ (v3_pre_topc @ X18 @ X21)
% 0.36/0.57          | ~ (r1_tarski @ X18 @ X19)
% 0.36/0.57          | ~ (r2_hidden @ X17 @ X18))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.57  thf('84', plain,
% 0.36/0.57      ((![X0 : $i, X1 : $i]:
% 0.36/0.57          (~ (r2_hidden @ X0 @ sk_D_2)
% 0.36/0.57           | ~ (r1_tarski @ sk_D_2 @ X1)
% 0.36/0.57           | ~ (v3_pre_topc @ sk_D_2 @ sk_A)
% 0.36/0.57           | (zip_tseitin_0 @ sk_D_2 @ X0 @ X1 @ sk_A)))
% 0.36/0.57         <= (((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['82', '83'])).
% 0.36/0.57  thf('85', plain,
% 0.36/0.57      ((![X0 : $i, X1 : $i]:
% 0.36/0.57          ((zip_tseitin_0 @ sk_D_2 @ X1 @ X0 @ sk_A)
% 0.36/0.57           | ~ (r1_tarski @ sk_D_2 @ X0)
% 0.36/0.57           | ~ (r2_hidden @ X1 @ sk_D_2)))
% 0.36/0.57         <= (((v3_pre_topc @ sk_D_2 @ sk_A)) & 
% 0.36/0.57             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['81', '84'])).
% 0.36/0.57  thf('86', plain,
% 0.36/0.57      ((![X0 : $i]:
% 0.36/0.57          (~ (r2_hidden @ X0 @ sk_D_2)
% 0.36/0.57           | (zip_tseitin_0 @ sk_D_2 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 0.36/0.57         <= (((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.36/0.57             ((v3_pre_topc @ sk_D_2 @ sk_A)) & 
% 0.36/0.57             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['80', '85'])).
% 0.36/0.57  thf('87', plain,
% 0.36/0.57      (((zip_tseitin_0 @ sk_D_2 @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))
% 0.36/0.57         <= (((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.36/0.57             ((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.36/0.57             ((v3_pre_topc @ sk_D_2 @ sk_A)) & 
% 0.36/0.57             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['46', '86'])).
% 0.36/0.57  thf('88', plain,
% 0.36/0.57      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.36/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.36/0.57  thf(zf_stmt_3, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v3_pre_topc @ B @ A ) <=>
% 0.36/0.57             ( ![C:$i]:
% 0.36/0.57               ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.57                 ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ))).
% 0.36/0.57  thf('89', plain,
% 0.36/0.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.36/0.57          | ~ (v3_pre_topc @ X22 @ X23)
% 0.36/0.57          | (r2_hidden @ X24 @ X22)
% 0.36/0.57          | ~ (zip_tseitin_0 @ X25 @ X24 @ X22 @ X23)
% 0.36/0.57          | ~ (l1_pre_topc @ X23)
% 0.36/0.57          | ~ (v2_pre_topc @ X23))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.57  thf('90', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (v2_pre_topc @ sk_A)
% 0.36/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.57          | ~ (zip_tseitin_0 @ X1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.36/0.57          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57          | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['88', '89'])).
% 0.36/0.57  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('93', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.57  thf('94', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         (~ (zip_tseitin_0 @ X1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.36/0.57          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.36/0.57      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.36/0.57  thf('95', plain,
% 0.36/0.57      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.36/0.57         <= (((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.36/0.57             ((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.36/0.57             ((v3_pre_topc @ sk_D_2 @ sk_A)) & 
% 0.36/0.57             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['87', '94'])).
% 0.36/0.57  thf('96', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('97', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.36/0.57          | ~ (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 0.36/0.57          | (m1_connsp_2 @ X30 @ X29 @ X28)
% 0.36/0.57          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.36/0.57          | ~ (l1_pre_topc @ X29)
% 0.36/0.57          | ~ (v2_pre_topc @ X29)
% 0.36/0.57          | (v2_struct_0 @ X29))),
% 0.36/0.57      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.57  thf('98', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v2_struct_0 @ sk_A)
% 0.36/0.57          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.57          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.57          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.57          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['96', '97'])).
% 0.36/0.57  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('101', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((v2_struct_0 @ sk_A)
% 0.36/0.57          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.36/0.57          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.36/0.57          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['98', '99', '100'])).
% 0.36/0.57  thf('102', plain,
% 0.36/0.57      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.57         | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.36/0.57         | (v2_struct_0 @ sk_A)))
% 0.36/0.57         <= (((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.36/0.57             ((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.36/0.57             ((v3_pre_topc @ sk_D_2 @ sk_A)) & 
% 0.36/0.57             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['95', '101'])).
% 0.36/0.57  thf('103', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('104', plain,
% 0.36/0.57      ((((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.36/0.57         <= (((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.36/0.57             ((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.36/0.57             ((v3_pre_topc @ sk_D_2 @ sk_A)) & 
% 0.36/0.57             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['102', '103'])).
% 0.36/0.57  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('106', plain,
% 0.36/0.57      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.57         <= (((r2_hidden @ sk_B @ sk_D_2)) & 
% 0.36/0.57             ((r1_tarski @ sk_D_2 @ sk_C_1)) & 
% 0.36/0.57             ((v3_pre_topc @ sk_D_2 @ sk_A)) & 
% 0.36/0.57             ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.36/0.57      inference('clc', [status(thm)], ['104', '105'])).
% 0.36/0.57  thf('107', plain,
% 0.36/0.57      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.36/0.57         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('split', [status(esa)], ['6'])).
% 0.36/0.57  thf('108', plain,
% 0.36/0.57      (~ ((v3_pre_topc @ sk_D_2 @ sk_A)) | 
% 0.36/0.57       ~ ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.36/0.57       ~ ((r1_tarski @ sk_D_2 @ sk_C_1)) | ~ ((r2_hidden @ sk_B @ sk_D_2)) | 
% 0.36/0.57       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['106', '107'])).
% 0.36/0.57  thf('109', plain, ($false),
% 0.36/0.57      inference('sat_resolution*', [status(thm)],
% 0.36/0.57                ['1', '3', '5', '7', '43', '45', '108'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

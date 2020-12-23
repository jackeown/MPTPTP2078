%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvWsNTIklQ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 214 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          : 1245 (3876 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X26 @ sk_A )
      | ~ ( r1_tarski @ X26 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X26 )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X12 @ X11 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
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
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('34',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['25','26'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('37',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X9 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('38',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
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
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(demod,[status(thm)],['34','35','41'])).

thf('43',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['19','42'])).

thf('44',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

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

thf('48',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X17 )
        = X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('49',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( v3_pre_topc @ X17 @ X16 )
        | ( ( k1_tops_1 @ X16 @ X17 )
          = X17 ) )
   <= ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( v3_pre_topc @ X17 @ X16 )
        | ( ( k1_tops_1 @ X16 @ X17 )
          = X17 ) ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X17 )
        = X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('52',plain,
    ( ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ~ ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ! [X16: $i,X17: $i] :
        ( ~ ( l1_pre_topc @ X16 )
        | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
        | ~ ( v3_pre_topc @ X17 @ X16 )
        | ( ( k1_tops_1 @ X16 @ X17 )
          = X17 ) )
    | ! [X18: $i,X19: $i] :
        ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
        | ~ ( l1_pre_topc @ X19 )
        | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(split,[status(esa)],['51'])).

thf('58',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X17 )
        = X17 ) ) ),
    inference('sat_resolution*',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X17 @ X16 )
      | ( ( k1_tops_1 @ X16 @ X17 )
        = X17 ) ) ),
    inference(simpl_trail,[status(thm)],['49','58'])).

thf('60',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_D )
        = sk_D )
      | ~ ( v3_pre_topc @ sk_D @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_D )
        = sk_D )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('67',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,
    ( ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['63','72'])).

thf('74',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('75',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X3 ) @ X5 )
      | ~ ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('76',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k1_tarski @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('81',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ ( k1_tops_1 @ X21 @ X22 ) )
      | ( m1_connsp_2 @ X22 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('94',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','43','45','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvWsNTIklQ
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:29:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 317 iterations in 0.099s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.19/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.54  thf(t8_connsp_2, conjecture,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.54                 ( ?[D:$i]:
% 0.19/0.54                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.19/0.54                     ( v3_pre_topc @ D @ A ) & 
% 0.19/0.54                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i]:
% 0.19/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.54            ( l1_pre_topc @ A ) ) =>
% 0.19/0.54          ( ![B:$i]:
% 0.19/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54              ( ![C:$i]:
% 0.19/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.54                    ( ?[D:$i]:
% 0.19/0.54                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.19/0.54                        ( v3_pre_topc @ D @ A ) & 
% 0.19/0.54                        ( m1_subset_1 @
% 0.19/0.54                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (((r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      (((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      (((r1_tarski @ sk_D @ sk_C) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (((r1_tarski @ sk_D @ sk_C)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('split', [status(esa)], ['2'])).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.19/0.54       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('split', [status(esa)], ['4'])).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X26 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54          | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.19/0.54          | ~ (r1_tarski @ X26 @ sk_C)
% 0.19/0.54          | ~ (r2_hidden @ sk_B @ X26)
% 0.19/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      ((![X26 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.19/0.54           | ~ (r1_tarski @ X26 @ sk_C)
% 0.19/0.54           | ~ (r2_hidden @ sk_B @ X26))) | 
% 0.19/0.54       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('split', [status(esa)], ['6'])).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(d1_connsp_2, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.54                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.19/0.54          | ~ (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.19/0.54          | (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.19/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.54          | ~ (l1_pre_topc @ X21)
% 0.19/0.54          | ~ (v2_pre_topc @ X21)
% 0.19/0.54          | (v2_struct_0 @ X21))),
% 0.19/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.54  thf('11', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.54  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.19/0.54  thf('15', plain,
% 0.19/0.54      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.54         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.54         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['8', '14'])).
% 0.19/0.54  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.19/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.54  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('19', plain,
% 0.19/0.54      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.54      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t3_subset, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      (![X6 : $i, X7 : $i]:
% 0.19/0.54         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.19/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.54  thf('22', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.54  thf('23', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(t44_tops_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (![X11 : $i, X12 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.19/0.54          | (r1_tarski @ (k1_tops_1 @ X12 @ X11) @ X11)
% 0.19/0.54          | ~ (l1_pre_topc @ X12))),
% 0.19/0.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.19/0.54  thf('25', plain,
% 0.19/0.54      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.19/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.54  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('27', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.19/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.54  thf(t1_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.54       ( r1_tarski @ A @ C ) ))).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.54          | (r1_tarski @ X0 @ X2))),
% 0.19/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 0.19/0.54          | ~ (r1_tarski @ sk_C @ X0))),
% 0.19/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.54  thf('30', plain,
% 0.19/0.54      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['22', '29'])).
% 0.19/0.54  thf('31', plain,
% 0.19/0.54      (![X6 : $i, X8 : $i]:
% 0.19/0.54         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.19/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.54  thf('32', plain,
% 0.19/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.19/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      ((![X26 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.19/0.54           | ~ (r1_tarski @ X26 @ sk_C)
% 0.19/0.54           | ~ (r2_hidden @ sk_B @ X26)))
% 0.19/0.54         <= ((![X26 : $i]:
% 0.19/0.54                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.19/0.54                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.19/0.54                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.19/0.54      inference('split', [status(esa)], ['6'])).
% 0.19/0.54  thf('34', plain,
% 0.19/0.54      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.54         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.19/0.54         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.19/0.54         <= ((![X26 : $i]:
% 0.19/0.54                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.19/0.54                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.19/0.54                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.54  thf('35', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.19/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.54  thf('36', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(fc9_tops_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.19/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.54       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.19/0.54  thf('37', plain,
% 0.19/0.54      (![X9 : $i, X10 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X9)
% 0.19/0.54          | ~ (v2_pre_topc @ X9)
% 0.19/0.54          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.19/0.54          | (v3_pre_topc @ (k1_tops_1 @ X9 @ X10) @ X9))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.19/0.54  thf('38', plain,
% 0.19/0.54      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.19/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.54  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('41', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.19/0.54      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.19/0.54  thf('42', plain,
% 0.19/0.54      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.54         <= ((![X26 : $i]:
% 0.19/0.54                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.19/0.54                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.19/0.54                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.19/0.54      inference('demod', [status(thm)], ['34', '35', '41'])).
% 0.19/0.54  thf('43', plain,
% 0.19/0.54      (~
% 0.19/0.54       (![X26 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.19/0.54           | ~ (r1_tarski @ X26 @ sk_C)
% 0.19/0.54           | ~ (r2_hidden @ sk_B @ X26))) | 
% 0.19/0.54       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['19', '42'])).
% 0.19/0.54  thf('44', plain,
% 0.19/0.54      (((v3_pre_topc @ sk_D @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('45', plain,
% 0.19/0.54      (((v3_pre_topc @ sk_D @ sk_A)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('split', [status(esa)], ['44'])).
% 0.19/0.54  thf('46', plain,
% 0.19/0.54      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.19/0.54      inference('split', [status(esa)], ['44'])).
% 0.19/0.54  thf('47', plain,
% 0.19/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.19/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('split', [status(esa)], ['4'])).
% 0.19/0.54  thf(t55_tops_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( l1_pre_topc @ B ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54               ( ![D:$i]:
% 0.19/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.54                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.19/0.54                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.19/0.54                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.19/0.54                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('48', plain,
% 0.19/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X16)
% 0.19/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54          | ~ (v3_pre_topc @ X17 @ X16)
% 0.19/0.54          | ((k1_tops_1 @ X16 @ X17) = (X17))
% 0.19/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54          | ~ (l1_pre_topc @ X19)
% 0.19/0.54          | ~ (v2_pre_topc @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.19/0.54  thf('49', plain,
% 0.19/0.54      ((![X16 : $i, X17 : $i]:
% 0.19/0.54          (~ (l1_pre_topc @ X16)
% 0.19/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54           | ~ (v3_pre_topc @ X17 @ X16)
% 0.19/0.54           | ((k1_tops_1 @ X16 @ X17) = (X17))))
% 0.19/0.54         <= ((![X16 : $i, X17 : $i]:
% 0.19/0.54                (~ (l1_pre_topc @ X16)
% 0.19/0.54                 | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54                 | ~ (v3_pre_topc @ X17 @ X16)
% 0.19/0.54                 | ((k1_tops_1 @ X16 @ X17) = (X17)))))),
% 0.19/0.54      inference('split', [status(esa)], ['48'])).
% 0.19/0.54  thf('50', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('51', plain,
% 0.19/0.54      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X16)
% 0.19/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54          | ~ (v3_pre_topc @ X17 @ X16)
% 0.19/0.54          | ((k1_tops_1 @ X16 @ X17) = (X17))
% 0.19/0.54          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54          | ~ (l1_pre_topc @ X19)
% 0.19/0.54          | ~ (v2_pre_topc @ X19))),
% 0.19/0.54      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.19/0.54  thf('52', plain,
% 0.19/0.54      ((![X18 : $i, X19 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54           | ~ (l1_pre_topc @ X19)
% 0.19/0.54           | ~ (v2_pre_topc @ X19)))
% 0.19/0.54         <= ((![X18 : $i, X19 : $i]:
% 0.19/0.54                (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54                 | ~ (l1_pre_topc @ X19)
% 0.19/0.54                 | ~ (v2_pre_topc @ X19))))),
% 0.19/0.54      inference('split', [status(esa)], ['51'])).
% 0.19/0.54  thf('53', plain,
% 0.19/0.54      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.19/0.54         <= ((![X18 : $i, X19 : $i]:
% 0.19/0.54                (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54                 | ~ (l1_pre_topc @ X19)
% 0.19/0.54                 | ~ (v2_pre_topc @ X19))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['50', '52'])).
% 0.19/0.54  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('56', plain,
% 0.19/0.54      (~
% 0.19/0.54       (![X18 : $i, X19 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54           | ~ (l1_pre_topc @ X19)
% 0.19/0.54           | ~ (v2_pre_topc @ X19)))),
% 0.19/0.54      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.19/0.54  thf('57', plain,
% 0.19/0.54      ((![X16 : $i, X17 : $i]:
% 0.19/0.54          (~ (l1_pre_topc @ X16)
% 0.19/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54           | ~ (v3_pre_topc @ X17 @ X16)
% 0.19/0.54           | ((k1_tops_1 @ X16 @ X17) = (X17)))) | 
% 0.19/0.54       (![X18 : $i, X19 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.19/0.54           | ~ (l1_pre_topc @ X19)
% 0.19/0.54           | ~ (v2_pre_topc @ X19)))),
% 0.19/0.54      inference('split', [status(esa)], ['51'])).
% 0.19/0.54  thf('58', plain,
% 0.19/0.54      ((![X16 : $i, X17 : $i]:
% 0.19/0.54          (~ (l1_pre_topc @ X16)
% 0.19/0.54           | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54           | ~ (v3_pre_topc @ X17 @ X16)
% 0.19/0.54           | ((k1_tops_1 @ X16 @ X17) = (X17))))),
% 0.19/0.54      inference('sat_resolution*', [status(thm)], ['56', '57'])).
% 0.19/0.54  thf('59', plain,
% 0.19/0.54      (![X16 : $i, X17 : $i]:
% 0.19/0.54         (~ (l1_pre_topc @ X16)
% 0.19/0.54          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.19/0.54          | ~ (v3_pre_topc @ X17 @ X16)
% 0.19/0.54          | ((k1_tops_1 @ X16 @ X17) = (X17)))),
% 0.19/0.54      inference('simpl_trail', [status(thm)], ['49', '58'])).
% 0.19/0.54  thf('60', plain,
% 0.19/0.54      (((((k1_tops_1 @ sk_A @ sk_D) = (sk_D))
% 0.19/0.54         | ~ (v3_pre_topc @ sk_D @ sk_A)
% 0.19/0.54         | ~ (l1_pre_topc @ sk_A)))
% 0.19/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['47', '59'])).
% 0.19/0.54  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('62', plain,
% 0.19/0.54      (((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)) | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.19/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.54  thf('63', plain,
% 0.19/0.54      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 0.19/0.54         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['46', '62'])).
% 0.19/0.54  thf('64', plain,
% 0.19/0.54      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.19/0.54      inference('split', [status(esa)], ['2'])).
% 0.19/0.54  thf('65', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('66', plain,
% 0.19/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.19/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('split', [status(esa)], ['4'])).
% 0.19/0.54  thf(t48_tops_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( l1_pre_topc @ A ) =>
% 0.19/0.54       ( ![B:$i]:
% 0.19/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.54               ( ( r1_tarski @ B @ C ) =>
% 0.19/0.54                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.54  thf('67', plain,
% 0.19/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.54          | ~ (r1_tarski @ X13 @ X15)
% 0.19/0.54          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ (k1_tops_1 @ X14 @ X15))
% 0.19/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.19/0.54          | ~ (l1_pre_topc @ X14))),
% 0.19/0.54      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.19/0.54  thf('68', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (l1_pre_topc @ sk_A)
% 0.19/0.54           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.19/0.54           | ~ (r1_tarski @ sk_D @ X0)))
% 0.19/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['66', '67'])).
% 0.19/0.54  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('70', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.54           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.19/0.54           | ~ (r1_tarski @ sk_D @ X0)))
% 0.19/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.19/0.54  thf('71', plain,
% 0.19/0.54      (((~ (r1_tarski @ sk_D @ sk_C)
% 0.19/0.54         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.19/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['65', '70'])).
% 0.19/0.54  thf('72', plain,
% 0.19/0.54      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.54         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['64', '71'])).
% 0.19/0.54  thf('73', plain,
% 0.19/0.54      (((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.54         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.19/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup+', [status(thm)], ['63', '72'])).
% 0.19/0.54  thf('74', plain,
% 0.19/0.54      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.54      inference('split', [status(esa)], ['0'])).
% 0.19/0.54  thf(l1_zfmisc_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.54  thf('75', plain,
% 0.19/0.54      (![X3 : $i, X5 : $i]:
% 0.19/0.54         ((r1_tarski @ (k1_tarski @ X3) @ X5) | ~ (r2_hidden @ X3 @ X5))),
% 0.19/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.54  thf('76', plain,
% 0.19/0.54      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_D))
% 0.19/0.54         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.54  thf('77', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.54          | (r1_tarski @ X0 @ X2))),
% 0.19/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.54  thf('78', plain,
% 0.19/0.54      ((![X0 : $i]:
% 0.19/0.54          ((r1_tarski @ (k1_tarski @ sk_B) @ X0) | ~ (r1_tarski @ sk_D @ X0)))
% 0.19/0.54         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['76', '77'])).
% 0.19/0.54  thf('79', plain,
% 0.19/0.54      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.19/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.19/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['73', '78'])).
% 0.19/0.54  thf('80', plain,
% 0.19/0.54      (![X3 : $i, X4 : $i]:
% 0.19/0.54         ((r2_hidden @ X3 @ X4) | ~ (r1_tarski @ (k1_tarski @ X3) @ X4))),
% 0.19/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.54  thf('81', plain,
% 0.19/0.54      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.19/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.19/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['79', '80'])).
% 0.19/0.54  thf('82', plain,
% 0.19/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('83', plain,
% 0.19/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.54         (~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 0.19/0.54          | ~ (r2_hidden @ X20 @ (k1_tops_1 @ X21 @ X22))
% 0.19/0.54          | (m1_connsp_2 @ X22 @ X21 @ X20)
% 0.19/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.54          | ~ (l1_pre_topc @ X21)
% 0.19/0.54          | ~ (v2_pre_topc @ X21)
% 0.19/0.54          | (v2_struct_0 @ X21))),
% 0.19/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.54  thf('84', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.19/0.54  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('87', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         ((v2_struct_0 @ sk_A)
% 0.19/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.54          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.54      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.19/0.54  thf('88', plain,
% 0.19/0.54      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.54         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.54         | (v2_struct_0 @ sk_A)))
% 0.19/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.19/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.19/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['81', '87'])).
% 0.19/0.54  thf('89', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('90', plain,
% 0.19/0.54      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B) | (v2_struct_0 @ sk_A)))
% 0.19/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.19/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.19/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('demod', [status(thm)], ['88', '89'])).
% 0.19/0.54  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('92', plain,
% 0.19/0.54      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.54         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.19/0.54             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.19/0.54             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 0.19/0.54             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.19/0.54      inference('clc', [status(thm)], ['90', '91'])).
% 0.19/0.54  thf('93', plain,
% 0.19/0.54      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.54         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.54      inference('split', [status(esa)], ['6'])).
% 0.19/0.54  thf('94', plain,
% 0.19/0.54      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.19/0.54       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.19/0.54       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 0.19/0.54       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.54      inference('sup-', [status(thm)], ['92', '93'])).
% 0.19/0.54  thf('95', plain, ($false),
% 0.19/0.54      inference('sat_resolution*', [status(thm)],
% 0.19/0.54                ['1', '3', '5', '7', '43', '45', '94'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

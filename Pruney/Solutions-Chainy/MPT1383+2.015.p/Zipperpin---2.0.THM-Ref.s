%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y6P2entozt

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 906 expanded)
%              Number of leaves         :   27 ( 249 expanded)
%              Depth                    :   20
%              Number of atoms          : 1190 (16563 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('0',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X31 @ sk_A )
      | ~ ( r1_tarski @ X31 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X31 )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_connsp_2 @ X20 @ X19 @ X18 )
      | ( r2_hidden @ X18 @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
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
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X31 ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X31 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X31 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
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
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X31 ) ) ),
    inference(demod,[status(thm)],['34','35','41'])).

thf('43',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X31 @ sk_A )
          | ~ ( r1_tarski @ X31 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X31 ) ) ),
    inference('sup-',[status(thm)],['19','42'])).

thf('44',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('45',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('47',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D @ X0 )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X31 ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X31 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D )
      | ~ ( r1_tarski @ sk_D @ sk_C )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X31 @ sk_A )
          | ~ ( r1_tarski @ X31 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X31 ) )
      & ( r1_tarski @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('56',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X31 @ sk_A )
          | ~ ( r1_tarski @ X31 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X31 ) )
      & ( r1_tarski @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
   <= ( ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X31 @ sk_A )
          | ~ ( r1_tarski @ X31 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X31 ) )
      & ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,
    ( ~ ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X31 @ sk_A )
          | ~ ( r1_tarski @ X31 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X31 ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['44','57'])).

thf('59',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X31 @ sk_A )
        | ~ ( r1_tarski @ X31 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X31 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('60',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','43','58','59'])).

thf('61',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['63'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','43','58','59','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['64','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( m1_connsp_2 @ C @ A @ B )
                      & ( m1_connsp_2 @ D @ A @ B ) )
                  <=> ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

thf('69',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X27 @ X26 ) @ X25 @ X24 )
      | ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_connsp_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X1 )
      | ~ ( m1_connsp_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X1 )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( k3_xboole_0 @ sk_D @ sk_C ) @ sk_A @ X0 )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = X3 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('80',plain,
    ( ( ( k3_xboole_0 @ sk_D @ sk_C )
      = sk_D )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['3','7','43','58','59','5'])).

thf('82',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','82'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m1_connsp_2 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['64','66'])).

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

thf('87',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X29 )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( m1_connsp_2 @ X28 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_D )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('92',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','5','43','58','59','7'])).

thf('93',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_D @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['88','89','90','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D )
    | ( m1_connsp_2 @ sk_D @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','94'])).

thf('96',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('97',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['5','7','43','58','59','3'])).

thf('98',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( m1_connsp_2 @ sk_D @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_connsp_2 @ sk_D @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['84','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['61','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Y6P2entozt
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:00:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 281 iterations in 0.072s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.54  thf(t8_connsp_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                 ( ?[D:$i]:
% 0.21/0.54                   ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.21/0.54                     ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.54            ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                  ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                    ( ?[D:$i]:
% 0.21/0.54                      ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.21/0.54                        ( v3_pre_topc @ D @ A ) & 
% 0.21/0.54                        ( m1_subset_1 @
% 0.21/0.54                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t8_connsp_2])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X31 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54          | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54          | ~ (r2_hidden @ sk_B @ X31)
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_D @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_D @ sk_A)) | ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d1_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.21/0.54                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.21/0.54          | ~ (m1_connsp_2 @ X20 @ X19 @ X18)
% 0.21/0.54          | (r2_hidden @ X18 @ (k1_tops_1 @ X19 @ X20))
% 0.21/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.54          | ~ (l1_pre_topc @ X19)
% 0.21/0.54          | ~ (v2_pre_topc @ X19)
% 0.21/0.54          | (v2_struct_0 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.54  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '14'])).
% 0.21/0.54  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.21/0.54      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i]:
% 0.21/0.54         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('22', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t44_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X16 : $i, X17 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.54          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.54          | ~ (l1_pre_topc @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.54  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('27', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf(t1_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.54       ( r1_tarski @ A @ C ) ))).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.54          | (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.54          | ~ (r1_tarski @ sk_C @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '29'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X8 : $i, X10 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.54        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((![X31 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X31)))
% 0.21/0.54         <= ((![X31 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X31))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.21/0.54         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.21/0.54         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.21/0.54         <= ((![X31 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X31))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.54  thf('35', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.21/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(fc9_tops_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X14 : $i, X15 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X14)
% 0.21/0.54          | ~ (v2_pre_topc @ X14)
% 0.21/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.54          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('41', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.21/0.54      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.21/0.54         <= ((![X31 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X31))))),
% 0.21/0.54      inference('demod', [status(thm)], ['34', '35', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.21/0.54       ~
% 0.21/0.54       (![X31 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X31)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['19', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('46', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.54          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.54          | (r1_tarski @ X0 @ X2))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      ((![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_C @ X0)))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (![X8 : $i, X10 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      ((![X31 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X31)))
% 0.21/0.54         <= ((![X31 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X31))))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (((~ (r2_hidden @ sk_B @ sk_D)
% 0.21/0.54         | ~ (r1_tarski @ sk_D @ sk_C)
% 0.21/0.54         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.21/0.54         <= ((![X31 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X31))) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (((~ (r2_hidden @ sk_B @ sk_D) | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.21/0.54         <= ((![X31 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X31))) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      ((~ (v3_pre_topc @ sk_D @ sk_A))
% 0.21/0.54         <= ((![X31 : $i]:
% 0.21/0.54                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54                 | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54                 | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54                 | ~ (r2_hidden @ sk_B @ X31))) & 
% 0.21/0.54             ((r2_hidden @ sk_B @ sk_D)) & 
% 0.21/0.54             ((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '56'])).
% 0.21/0.54  thf('58', plain,
% 0.21/0.54      (~
% 0.21/0.54       (![X31 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X31))) | 
% 0.21/0.54       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 0.21/0.54       ~ ((v3_pre_topc @ sk_D @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '57'])).
% 0.21/0.54  thf('59', plain,
% 0.21/0.54      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.21/0.54       (![X31 : $i]:
% 0.21/0.54          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54           | ~ (v3_pre_topc @ X31 @ sk_A)
% 0.21/0.54           | ~ (r1_tarski @ X31 @ sk_C)
% 0.21/0.54           | ~ (r2_hidden @ sk_B @ X31)))),
% 0.21/0.54      inference('split', [status(esa)], ['0'])).
% 0.21/0.54  thf('60', plain, (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)],
% 0.21/0.54                ['3', '5', '7', '43', '58', '59'])).
% 0.21/0.54  thf('61', plain, (~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['1', '60'])).
% 0.21/0.54  thf('62', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('64', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.54      inference('split', [status(esa)], ['63'])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.54       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('split', [status(esa)], ['63'])).
% 0.21/0.54  thf('66', plain,
% 0.21/0.54      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)],
% 0.21/0.54                ['3', '5', '7', '43', '58', '59', '65'])).
% 0.21/0.54  thf('67', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t4_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54               ( ![D:$i]:
% 0.21/0.54                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.21/0.54                       ( m1_connsp_2 @ D @ A @ B ) ) <=>
% 0.21/0.54                     ( m1_connsp_2 @
% 0.21/0.54                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('69', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.21/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.54          | ~ (m1_connsp_2 @ (k9_subset_1 @ (u1_struct_0 @ X25) @ X27 @ X26) @ 
% 0.21/0.54               X25 @ X24)
% 0.21/0.54          | (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.21/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.21/0.54          | ~ (l1_pre_topc @ X25)
% 0.21/0.54          | ~ (v2_pre_topc @ X25)
% 0.21/0.54          | (v2_struct_0 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [t4_connsp_2])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X1)
% 0.21/0.54          | ~ (m1_connsp_2 @ 
% 0.21/0.54               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ sk_A @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.54         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 0.21/0.54          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.21/0.54           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.21/0.54      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X1)
% 0.21/0.54          | ~ (m1_connsp_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A @ X1)
% 0.21/0.54          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['70', '71', '72', '75'])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (m1_connsp_2 @ (k3_xboole_0 @ sk_D @ sk_C) @ sk_A @ X0)
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['67', '76'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('split', [status(esa)], ['4'])).
% 0.21/0.54  thf(t28_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      (![X3 : $i, X4 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X3 @ X4) = (X3)) | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      ((((k3_xboole_0 @ sk_D @ sk_C) = (sk_D)))
% 0.21/0.54         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.54  thf('81', plain, (((r1_tarski @ sk_D @ sk_C))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)],
% 0.21/0.54                ['3', '7', '43', '58', '59', '5'])).
% 0.21/0.54  thf('82', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.21/0.54  thf('83', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | ~ (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.21/0.54          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.21/0.54          | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['77', '82'])).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.21/0.54        | ~ (m1_connsp_2 @ sk_D @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['62', '83'])).
% 0.21/0.54  thf('85', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('86', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.21/0.54  thf(t5_connsp_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54               ( ( ( v3_pre_topc @ B @ A ) & ( r2_hidden @ C @ B ) ) =>
% 0.21/0.54                 ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.21/0.54          | ~ (v3_pre_topc @ X28 @ X29)
% 0.21/0.54          | ~ (r2_hidden @ X30 @ X28)
% 0.21/0.54          | (m1_connsp_2 @ X28 @ X29 @ X30)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.21/0.54          | ~ (l1_pre_topc @ X29)
% 0.21/0.54          | ~ (v2_pre_topc @ X29)
% 0.21/0.54          | (v2_struct_0 @ X29))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_connsp_2])).
% 0.21/0.54  thf('88', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.54          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_D)
% 0.21/0.54          | ~ (v3_pre_topc @ sk_D @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.54  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['6'])).
% 0.21/0.54  thf('92', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)],
% 0.21/0.54                ['3', '5', '43', '58', '59', '7'])).
% 0.21/0.54  thf('93', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['91', '92'])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v2_struct_0 @ sk_A)
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54          | (m1_connsp_2 @ sk_D @ sk_A @ X0)
% 0.21/0.54          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.21/0.54      inference('demod', [status(thm)], ['88', '89', '90', '93'])).
% 0.21/0.54  thf('95', plain,
% 0.21/0.54      ((~ (r2_hidden @ sk_B @ sk_D)
% 0.21/0.54        | (m1_connsp_2 @ sk_D @ sk_A @ sk_B)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['85', '94'])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.21/0.54      inference('split', [status(esa)], ['2'])).
% 0.21/0.54  thf('97', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)],
% 0.21/0.54                ['5', '7', '43', '58', '59', '3'])).
% 0.21/0.54  thf('98', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      (((m1_connsp_2 @ sk_D @ sk_A @ sk_B) | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['95', '98'])).
% 0.21/0.54  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('101', plain, ((m1_connsp_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.54      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A) | (m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.21/0.54      inference('demod', [status(thm)], ['84', '101'])).
% 0.21/0.54  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('104', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.54      inference('clc', [status(thm)], ['102', '103'])).
% 0.21/0.54  thf('105', plain, ($false), inference('demod', [status(thm)], ['61', '104'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

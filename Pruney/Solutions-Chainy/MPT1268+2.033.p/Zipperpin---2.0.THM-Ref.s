%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nyb6MTthu2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:20 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 177 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  897 (2415 expanded)
%              Number of equality atoms :   36 (  92 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('0',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( r1_tarski @ X30 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('24',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','21','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X29 @ X28 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ~ ! [X30: $i] :
          ( ( X30 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tops_1 @ X28 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X28 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('47',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('48',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('50',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B_1 @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t54_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X24 )
      | ~ ( v3_pre_topc @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r2_hidden @ X26 @ ( k1_tops_1 @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t54_tops_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X1 @ sk_A )
      | ~ ( r1_tarski @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( r1_tarski @ sk_C @ sk_B_1 )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_C )
        | ~ ( v3_pre_topc @ sk_C @ sk_A )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','64'])).

thf('66',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','65'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('68',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( sk_B @ sk_C ) ) )
   <= ( ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ ( sk_B @ sk_C ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','68'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('70',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('71',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B_1 @ sk_A )
      & ( r1_tarski @ sk_C @ sk_B_1 )
      & ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','37','39','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nyb6MTthu2
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.02/1.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.19  % Solved by: fo/fo7.sh
% 1.02/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.19  % done 2304 iterations in 0.739s
% 1.02/1.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.19  % SZS output start Refutation
% 1.02/1.19  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.02/1.19  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.02/1.19  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.02/1.19  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.02/1.19  thf(sk_B_type, type, sk_B: $i > $i).
% 1.02/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.02/1.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.19  thf(sk_C_type, type, sk_C: $i).
% 1.02/1.19  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.02/1.19  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.02/1.19  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.19  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.02/1.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.19  thf(t86_tops_1, conjecture,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( v2_tops_1 @ B @ A ) <=>
% 1.02/1.19             ( ![C:$i]:
% 1.02/1.19               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.02/1.19                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 1.02/1.19  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.19    (~( ![A:$i]:
% 1.02/1.19        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.19          ( ![B:$i]:
% 1.02/1.19            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19              ( ( v2_tops_1 @ B @ A ) <=>
% 1.02/1.19                ( ![C:$i]:
% 1.02/1.19                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 1.02/1.19                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 1.02/1.19    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 1.02/1.19  thf('0', plain,
% 1.02/1.19      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('1', plain,
% 1.02/1.19      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('split', [status(esa)], ['0'])).
% 1.02/1.19  thf('2', plain,
% 1.02/1.19      (((r1_tarski @ sk_C @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('3', plain,
% 1.02/1.19      (((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('split', [status(esa)], ['2'])).
% 1.02/1.19  thf('4', plain,
% 1.02/1.19      (![X30 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19          | ((X30) = (k1_xboole_0))
% 1.02/1.19          | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19          | ~ (r1_tarski @ X30 @ sk_B_1)
% 1.02/1.19          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('5', plain,
% 1.02/1.19      ((![X30 : $i]:
% 1.02/1.19          (((X30) = (k1_xboole_0))
% 1.02/1.19           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19           | ~ (r1_tarski @ X30 @ sk_B_1))) | 
% 1.02/1.19       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('split', [status(esa)], ['4'])).
% 1.02/1.19  thf('6', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t3_subset, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.19  thf('7', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('8', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.02/1.19  thf('9', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t44_tops_1, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( l1_pre_topc @ A ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.02/1.19  thf('10', plain,
% 1.02/1.19      (![X22 : $i, X23 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.02/1.19          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 1.02/1.19          | ~ (l1_pre_topc @ X23))),
% 1.02/1.19      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.02/1.19  thf('11', plain,
% 1.02/1.19      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.19        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 1.02/1.19      inference('sup-', [status(thm)], ['9', '10'])).
% 1.02/1.19  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('13', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 1.02/1.19      inference('demod', [status(thm)], ['11', '12'])).
% 1.02/1.19  thf(t1_xboole_1, axiom,
% 1.02/1.19    (![A:$i,B:$i,C:$i]:
% 1.02/1.19     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.02/1.19       ( r1_tarski @ A @ C ) ))).
% 1.02/1.19  thf('14', plain,
% 1.02/1.19      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.02/1.19         (~ (r1_tarski @ X3 @ X4)
% 1.02/1.19          | ~ (r1_tarski @ X4 @ X5)
% 1.02/1.19          | (r1_tarski @ X3 @ X5))),
% 1.02/1.19      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.02/1.19  thf('15', plain,
% 1.02/1.19      (![X0 : $i]:
% 1.02/1.19         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 1.02/1.19          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 1.02/1.19      inference('sup-', [status(thm)], ['13', '14'])).
% 1.02/1.19  thf('16', plain,
% 1.02/1.19      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['8', '15'])).
% 1.02/1.19  thf('17', plain,
% 1.02/1.19      (![X7 : $i, X9 : $i]:
% 1.02/1.19         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('18', plain,
% 1.02/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 1.02/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['16', '17'])).
% 1.02/1.19  thf('19', plain,
% 1.02/1.19      ((![X30 : $i]:
% 1.02/1.19          (((X30) = (k1_xboole_0))
% 1.02/1.19           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19           | ~ (r1_tarski @ X30 @ sk_B_1)))
% 1.02/1.19         <= ((![X30 : $i]:
% 1.02/1.19                (((X30) = (k1_xboole_0))
% 1.02/1.19                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 1.02/1.19      inference('split', [status(esa)], ['4'])).
% 1.02/1.19  thf('20', plain,
% 1.02/1.19      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 1.02/1.19         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 1.02/1.19         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 1.02/1.19         <= ((![X30 : $i]:
% 1.02/1.19                (((X30) = (k1_xboole_0))
% 1.02/1.19                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['18', '19'])).
% 1.02/1.19  thf('21', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 1.02/1.19      inference('demod', [status(thm)], ['11', '12'])).
% 1.02/1.19  thf('22', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(fc9_tops_1, axiom,
% 1.02/1.19    (![A:$i,B:$i]:
% 1.02/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.02/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.19       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.02/1.19  thf('23', plain,
% 1.02/1.19      (![X20 : $i, X21 : $i]:
% 1.02/1.19         (~ (l1_pre_topc @ X20)
% 1.02/1.19          | ~ (v2_pre_topc @ X20)
% 1.02/1.19          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.02/1.19          | (v3_pre_topc @ (k1_tops_1 @ X20 @ X21) @ X20))),
% 1.02/1.19      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.02/1.19  thf('24', plain,
% 1.02/1.19      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 1.02/1.19        | ~ (v2_pre_topc @ sk_A)
% 1.02/1.19        | ~ (l1_pre_topc @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['22', '23'])).
% 1.02/1.19  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('27', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 1.02/1.19      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.02/1.19  thf('28', plain,
% 1.02/1.19      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 1.02/1.19         <= ((![X30 : $i]:
% 1.02/1.19                (((X30) = (k1_xboole_0))
% 1.02/1.19                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 1.02/1.19      inference('demod', [status(thm)], ['20', '21', '27'])).
% 1.02/1.19  thf('29', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t84_tops_1, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( l1_pre_topc @ A ) =>
% 1.02/1.19       ( ![B:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( v2_tops_1 @ B @ A ) <=>
% 1.02/1.19             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.02/1.19  thf('30', plain,
% 1.02/1.19      (![X28 : $i, X29 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.02/1.19          | ((k1_tops_1 @ X29 @ X28) != (k1_xboole_0))
% 1.02/1.19          | (v2_tops_1 @ X28 @ X29)
% 1.02/1.19          | ~ (l1_pre_topc @ X29))),
% 1.02/1.19      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.02/1.19  thf('31', plain,
% 1.02/1.19      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.19        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 1.02/1.19        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['29', '30'])).
% 1.02/1.19  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('33', plain,
% 1.02/1.19      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 1.02/1.19        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 1.02/1.19      inference('demod', [status(thm)], ['31', '32'])).
% 1.02/1.19  thf('34', plain,
% 1.02/1.19      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 1.02/1.19         <= ((![X30 : $i]:
% 1.02/1.19                (((X30) = (k1_xboole_0))
% 1.02/1.19                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 1.02/1.19      inference('sup-', [status(thm)], ['28', '33'])).
% 1.02/1.19  thf('35', plain,
% 1.02/1.19      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 1.02/1.19         <= ((![X30 : $i]:
% 1.02/1.19                (((X30) = (k1_xboole_0))
% 1.02/1.19                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 1.02/1.19      inference('simplify', [status(thm)], ['34'])).
% 1.02/1.19  thf('36', plain,
% 1.02/1.19      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.19      inference('split', [status(esa)], ['2'])).
% 1.02/1.19  thf('37', plain,
% 1.02/1.19      (~
% 1.02/1.19       (![X30 : $i]:
% 1.02/1.19          (((X30) = (k1_xboole_0))
% 1.02/1.19           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19           | ~ (v3_pre_topc @ X30 @ sk_A)
% 1.02/1.19           | ~ (r1_tarski @ X30 @ sk_B_1))) | 
% 1.02/1.19       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['35', '36'])).
% 1.02/1.19  thf('38', plain,
% 1.02/1.19      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('39', plain,
% 1.02/1.19      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('split', [status(esa)], ['38'])).
% 1.02/1.19  thf('40', plain,
% 1.02/1.19      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.19      inference('split', [status(esa)], ['4'])).
% 1.02/1.19  thf('41', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('42', plain,
% 1.02/1.19      (![X28 : $i, X29 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.02/1.19          | ~ (v2_tops_1 @ X28 @ X29)
% 1.02/1.19          | ((k1_tops_1 @ X29 @ X28) = (k1_xboole_0))
% 1.02/1.19          | ~ (l1_pre_topc @ X29))),
% 1.02/1.19      inference('cnf', [status(esa)], [t84_tops_1])).
% 1.02/1.19  thf('43', plain,
% 1.02/1.19      ((~ (l1_pre_topc @ sk_A)
% 1.02/1.19        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 1.02/1.19        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['41', '42'])).
% 1.02/1.19  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('45', plain,
% 1.02/1.19      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 1.02/1.19        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 1.02/1.19      inference('demod', [status(thm)], ['43', '44'])).
% 1.02/1.19  thf('46', plain,
% 1.02/1.19      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 1.02/1.19         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['40', '45'])).
% 1.02/1.19  thf(t34_mcart_1, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.02/1.19          ( ![B:$i]:
% 1.02/1.19            ( ~( ( r2_hidden @ B @ A ) & 
% 1.02/1.19                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 1.02/1.19                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.02/1.19                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 1.02/1.19  thf('47', plain,
% 1.02/1.19      (![X15 : $i]:
% 1.02/1.19         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 1.02/1.19      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.02/1.19  thf('48', plain,
% 1.02/1.19      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 1.02/1.19      inference('split', [status(esa)], ['38'])).
% 1.02/1.19  thf('49', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.02/1.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.02/1.19  thf('50', plain,
% 1.02/1.19      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 1.02/1.19      inference('split', [status(esa)], ['2'])).
% 1.02/1.19  thf('51', plain,
% 1.02/1.19      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.02/1.19         (~ (r1_tarski @ X3 @ X4)
% 1.02/1.19          | ~ (r1_tarski @ X4 @ X5)
% 1.02/1.19          | (r1_tarski @ X3 @ X5))),
% 1.02/1.19      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.02/1.19  thf('52', plain,
% 1.02/1.19      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B_1 @ X0)))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['50', '51'])).
% 1.02/1.19  thf('53', plain,
% 1.02/1.19      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['49', '52'])).
% 1.02/1.19  thf('54', plain,
% 1.02/1.19      (![X7 : $i, X9 : $i]:
% 1.02/1.19         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('55', plain,
% 1.02/1.19      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['53', '54'])).
% 1.02/1.19  thf('56', plain,
% 1.02/1.19      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf(t54_tops_1, axiom,
% 1.02/1.19    (![A:$i]:
% 1.02/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.19       ( ![B:$i,C:$i]:
% 1.02/1.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.19           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 1.02/1.19             ( ?[D:$i]:
% 1.02/1.19               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 1.02/1.19                 ( v3_pre_topc @ D @ A ) & 
% 1.02/1.19                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.02/1.19  thf('57', plain,
% 1.02/1.19      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.02/1.19         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.02/1.19          | ~ (r2_hidden @ X26 @ X27)
% 1.02/1.19          | ~ (r1_tarski @ X27 @ X24)
% 1.02/1.19          | ~ (v3_pre_topc @ X27 @ X25)
% 1.02/1.19          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.02/1.19          | (r2_hidden @ X26 @ (k1_tops_1 @ X25 @ X24))
% 1.02/1.19          | ~ (l1_pre_topc @ X25)
% 1.02/1.19          | ~ (v2_pre_topc @ X25))),
% 1.02/1.19      inference('cnf', [status(esa)], [t54_tops_1])).
% 1.02/1.19  thf('58', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         (~ (v2_pre_topc @ sk_A)
% 1.02/1.19          | ~ (l1_pre_topc @ sk_A)
% 1.02/1.19          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 1.02/1.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19          | ~ (v3_pre_topc @ X1 @ sk_A)
% 1.02/1.19          | ~ (r1_tarski @ X1 @ sk_B_1)
% 1.02/1.19          | ~ (r2_hidden @ X0 @ X1))),
% 1.02/1.19      inference('sup-', [status(thm)], ['56', '57'])).
% 1.02/1.19  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.19  thf('61', plain,
% 1.02/1.19      (![X0 : $i, X1 : $i]:
% 1.02/1.19         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 1.02/1.19          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.02/1.19          | ~ (v3_pre_topc @ X1 @ sk_A)
% 1.02/1.19          | ~ (r1_tarski @ X1 @ sk_B_1)
% 1.02/1.19          | ~ (r2_hidden @ X0 @ X1))),
% 1.02/1.19      inference('demod', [status(thm)], ['58', '59', '60'])).
% 1.02/1.19  thf('62', plain,
% 1.02/1.19      ((![X0 : $i]:
% 1.02/1.19          (~ (r2_hidden @ X0 @ sk_C)
% 1.02/1.19           | ~ (r1_tarski @ sk_C @ sk_B_1)
% 1.02/1.19           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 1.02/1.19           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['55', '61'])).
% 1.02/1.19  thf('63', plain,
% 1.02/1.19      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 1.02/1.19      inference('split', [status(esa)], ['2'])).
% 1.02/1.19  thf('64', plain,
% 1.02/1.19      ((![X0 : $i]:
% 1.02/1.19          (~ (r2_hidden @ X0 @ sk_C)
% 1.02/1.19           | ~ (v3_pre_topc @ sk_C @ sk_A)
% 1.02/1.19           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 1.02/1.19      inference('demod', [status(thm)], ['62', '63'])).
% 1.02/1.19  thf('65', plain,
% 1.02/1.19      ((![X0 : $i]:
% 1.02/1.19          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B_1))
% 1.02/1.19           | ~ (r2_hidden @ X0 @ sk_C)))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['48', '64'])).
% 1.02/1.19  thf('66', plain,
% 1.02/1.19      (((((sk_C) = (k1_xboole_0))
% 1.02/1.19         | (r2_hidden @ (sk_B @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['47', '65'])).
% 1.02/1.19  thf(t7_ordinal1, axiom,
% 1.02/1.19    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.02/1.19  thf('67', plain,
% 1.02/1.19      (![X13 : $i, X14 : $i]:
% 1.02/1.19         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 1.02/1.19      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.02/1.19  thf('68', plain,
% 1.02/1.19      (((((sk_C) = (k1_xboole_0))
% 1.02/1.19         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (sk_B @ sk_C))))
% 1.02/1.19         <= (((r1_tarski @ sk_C @ sk_B_1)) & ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['66', '67'])).
% 1.02/1.19  thf('69', plain,
% 1.02/1.19      (((~ (r1_tarski @ k1_xboole_0 @ (sk_B @ sk_C)) | ((sk_C) = (k1_xboole_0))))
% 1.02/1.19         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 1.02/1.19             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 1.02/1.19             ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['46', '68'])).
% 1.02/1.19  thf(t4_subset_1, axiom,
% 1.02/1.19    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.02/1.19  thf('70', plain,
% 1.02/1.19      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 1.02/1.19      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.02/1.19  thf('71', plain,
% 1.02/1.19      (![X7 : $i, X8 : $i]:
% 1.02/1.19         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.02/1.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.19  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.02/1.19      inference('sup-', [status(thm)], ['70', '71'])).
% 1.02/1.19  thf('73', plain,
% 1.02/1.19      ((((sk_C) = (k1_xboole_0)))
% 1.02/1.19         <= (((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 1.02/1.19             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 1.02/1.19             ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.02/1.19      inference('demod', [status(thm)], ['69', '72'])).
% 1.02/1.19  thf('74', plain,
% 1.02/1.19      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 1.02/1.19      inference('split', [status(esa)], ['0'])).
% 1.02/1.19  thf('75', plain,
% 1.02/1.19      ((((sk_C) != (sk_C)))
% 1.02/1.19         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 1.02/1.19             ((v2_tops_1 @ sk_B_1 @ sk_A)) & 
% 1.02/1.19             ((r1_tarski @ sk_C @ sk_B_1)) & 
% 1.02/1.19             ((v3_pre_topc @ sk_C @ sk_A)))),
% 1.02/1.19      inference('sup-', [status(thm)], ['73', '74'])).
% 1.02/1.19  thf('76', plain,
% 1.02/1.19      (~ ((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 1.02/1.19       ~ ((r1_tarski @ sk_C @ sk_B_1)) | (((sk_C) = (k1_xboole_0)))),
% 1.02/1.19      inference('simplify', [status(thm)], ['75'])).
% 1.02/1.19  thf('77', plain, ($false),
% 1.02/1.19      inference('sat_resolution*', [status(thm)],
% 1.02/1.19                ['1', '3', '5', '37', '39', '76'])).
% 1.02/1.19  
% 1.02/1.19  % SZS output end Refutation
% 1.02/1.19  
% 1.02/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

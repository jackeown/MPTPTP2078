%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hQzTKMgYTr

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:17 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 168 expanded)
%              Number of leaves         :   24 (  55 expanded)
%              Depth                    :   16
%              Number of atoms          :  900 (2353 expanded)
%              Number of equality atoms :   33 (  87 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

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
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X20 @ sk_A )
      | ~ ( r1_tarski @ X20 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tops_1 @ X18 @ X19 )
      | ( ( k1_tops_1 @ X19 @ X18 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_C_1 @ sk_A )
   <= ( v3_pre_topc @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ( r1_tarski @ X15 @ ( k1_tops_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C_1 @ X0 )
        | ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_C_1 @ sk_B ) )
   <= ( ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_C_1 @ k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['15','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('33',plain,
    ( ( sk_C_1 != sk_C_1 )
   <= ( ( sk_C_1 != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A )
      & ( r1_tarski @ sk_C_1 @ sk_B )
      & ( v3_pre_topc @ sk_C_1 @ sk_A )
      & ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v3_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( r1_tarski @ sk_C_1 @ sk_B )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X14 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('57',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X11 @ X12 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('61',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X20: $i] :
        ( ( X20 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X20 @ sk_A )
        | ~ ( r1_tarski @ X20 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('74',plain,
    ( ~ ! [X20: $i] :
          ( ( X20 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X20 @ sk_A )
          | ~ ( r1_tarski @ X20 @ sk_B ) )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','34','35','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hQzTKMgYTr
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:13:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 693 iterations in 0.221s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.48/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.48/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.68  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.48/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.68  thf(t86_tops_1, conjecture,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.48/0.68             ( ![C:$i]:
% 0.48/0.68               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.48/0.68                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.68    (~( ![A:$i]:
% 0.48/0.68        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68          ( ![B:$i]:
% 0.48/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68              ( ( v2_tops_1 @ B @ A ) <=>
% 0.48/0.68                ( ![C:$i]:
% 0.48/0.68                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.48/0.68                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (((v3_pre_topc @ sk_C_1 @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (((r1_tarski @ sk_C_1 @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (((r1_tarski @ sk_C_1 @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['2'])).
% 0.48/0.68  thf('4', plain,
% 0.48/0.68      ((((sk_C_1) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (~ (((sk_C_1) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['4'])).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.48/0.68       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['6'])).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X20 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68          | ((X20) = (k1_xboole_0))
% 0.48/0.68          | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68          | ~ (r1_tarski @ X20 @ sk_B)
% 0.48/0.68          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('9', plain,
% 0.48/0.68      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['8'])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t84_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v2_tops_1 @ B @ A ) <=>
% 0.48/0.68             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X18 : $i, X19 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.48/0.68          | ~ (v2_tops_1 @ X18 @ X19)
% 0.48/0.68          | ((k1_tops_1 @ X19 @ X18) = (k1_xboole_0))
% 0.48/0.68          | ~ (l1_pre_topc @ X19))),
% 0.48/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.48/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.68  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('14', plain,
% 0.48/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.48/0.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.48/0.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['9', '14'])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      (((r1_tarski @ sk_C_1 @ sk_B)) <= (((r1_tarski @ sk_C_1 @ sk_B)))),
% 0.48/0.68      inference('split', [status(esa)], ['2'])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (((v3_pre_topc @ sk_C_1 @ sk_A)) <= (((v3_pre_topc @ sk_C_1 @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['0'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.48/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('split', [status(esa)], ['6'])).
% 0.48/0.68  thf(t56_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ![C:$i]:
% 0.48/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.48/0.68                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.48/0.68          | ~ (v3_pre_topc @ X15 @ X16)
% 0.48/0.68          | ~ (r1_tarski @ X15 @ X17)
% 0.48/0.68          | (r1_tarski @ X15 @ (k1_tops_1 @ X16 @ X17))
% 0.48/0.68          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.48/0.68          | ~ (l1_pre_topc @ X16))),
% 0.48/0.68      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (l1_pre_topc @ sk_A)
% 0.48/0.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.48/0.68           | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.48/0.68           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 0.48/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.48/0.68  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.48/0.68           | ~ (r1_tarski @ sk_C_1 @ X0)
% 0.48/0.68           | ~ (v3_pre_topc @ sk_C_1 @ sk_A)))
% 0.48/0.68         <= (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('demod', [status(thm)], ['21', '22'])).
% 0.48/0.68  thf('24', plain,
% 0.48/0.68      ((![X0 : $i]:
% 0.48/0.68          (~ (r1_tarski @ sk_C_1 @ X0)
% 0.48/0.68           | (r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ X0))
% 0.48/0.68           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.48/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.48/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['18', '23'])).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      ((((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B))
% 0.48/0.68         | ~ (r1_tarski @ sk_C_1 @ sk_B)))
% 0.48/0.68         <= (((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.48/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['17', '24'])).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (((r1_tarski @ sk_C_1 @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.48/0.68         <= (((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.48/0.68             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.48/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['16', '25'])).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (((r1_tarski @ sk_C_1 @ k1_xboole_0))
% 0.48/0.68         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.48/0.68             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.48/0.68             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.48/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('sup+', [status(thm)], ['15', '26'])).
% 0.48/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.68  thf('28', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.48/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.68  thf(d10_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (![X4 : $i, X6 : $i]:
% 0.48/0.68         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      ((((sk_C_1) = (k1_xboole_0)))
% 0.48/0.68         <= (((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.48/0.68             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.48/0.68             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.48/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['27', '30'])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.48/0.68      inference('split', [status(esa)], ['4'])).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      ((((sk_C_1) != (sk_C_1)))
% 0.48/0.68         <= (~ (((sk_C_1) = (k1_xboole_0))) & 
% 0.48/0.68             ((v2_tops_1 @ sk_B @ sk_A)) & 
% 0.48/0.68             ((r1_tarski @ sk_C_1 @ sk_B)) & 
% 0.48/0.68             ((v3_pre_topc @ sk_C_1 @ sk_A)) & 
% 0.48/0.68             ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (~ ((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.48/0.68       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.48/0.68       ~ ((v3_pre_topc @ sk_C_1 @ sk_A)) | ~ ((r1_tarski @ sk_C_1 @ sk_B)) | 
% 0.48/0.68       (((sk_C_1) = (k1_xboole_0)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['33'])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      ((![X20 : $i]:
% 0.48/0.68          (((X20) = (k1_xboole_0))
% 0.48/0.68           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68           | ~ (r1_tarski @ X20 @ sk_B))) | 
% 0.48/0.68       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('split', [status(esa)], ['8'])).
% 0.48/0.68  thf(d3_tarski, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X1 : $i, X3 : $i]:
% 0.48/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t44_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (![X13 : $i, X14 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.48/0.68          | (r1_tarski @ (k1_tops_1 @ X14 @ X13) @ X13)
% 0.48/0.68          | ~ (l1_pre_topc @ X14))),
% 0.48/0.68      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.68  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('41', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.48/0.68      inference('demod', [status(thm)], ['39', '40'])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.68          | (r2_hidden @ X0 @ X2)
% 0.48/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf('43', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r2_hidden @ X0 @ sk_B)
% 0.48/0.68          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.48/0.68  thf('44', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.48/0.68          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['36', '43'])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t3_subset, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.68  thf('46', plain,
% 0.48/0.68      (![X8 : $i, X9 : $i]:
% 0.48/0.68         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('47', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.48/0.68  thf('48', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.48/0.68          | (r2_hidden @ X0 @ X2)
% 0.48/0.68          | ~ (r1_tarski @ X1 @ X2))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf('49', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.48/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.68  thf('50', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.48/0.68          | (r2_hidden @ (sk_C @ X0 @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.48/0.68             (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['44', '49'])).
% 0.48/0.68  thf('51', plain,
% 0.48/0.68      (![X1 : $i, X3 : $i]:
% 0.48/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.68  thf('52', plain,
% 0.48/0.68      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.48/0.68        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.48/0.68  thf('53', plain,
% 0.48/0.68      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.48/0.68      inference('simplify', [status(thm)], ['52'])).
% 0.48/0.68  thf('54', plain,
% 0.48/0.68      (![X8 : $i, X10 : $i]:
% 0.48/0.68         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('55', plain,
% 0.48/0.68      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.48/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.68  thf('56', plain,
% 0.48/0.68      ((![X20 : $i]:
% 0.48/0.68          (((X20) = (k1_xboole_0))
% 0.48/0.68           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68           | ~ (r1_tarski @ X20 @ sk_B)))
% 0.48/0.68         <= ((![X20 : $i]:
% 0.48/0.68                (((X20) = (k1_xboole_0))
% 0.48/0.68                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.48/0.68      inference('split', [status(esa)], ['8'])).
% 0.48/0.68  thf('57', plain,
% 0.48/0.68      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.48/0.68         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.48/0.68         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.48/0.68         <= ((![X20 : $i]:
% 0.48/0.68                (((X20) = (k1_xboole_0))
% 0.48/0.68                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.48/0.68  thf('58', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.48/0.68      inference('demod', [status(thm)], ['39', '40'])).
% 0.48/0.68  thf('59', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(fc9_tops_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.48/0.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.68       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.48/0.68  thf('60', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X11)
% 0.48/0.68          | ~ (v2_pre_topc @ X11)
% 0.48/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.48/0.68          | (v3_pre_topc @ (k1_tops_1 @ X11 @ X12) @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.48/0.68  thf('61', plain,
% 0.48/0.68      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.48/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['59', '60'])).
% 0.48/0.68  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('64', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.48/0.68      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.48/0.68  thf('65', plain,
% 0.48/0.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.48/0.68         <= ((![X20 : $i]:
% 0.48/0.68                (((X20) = (k1_xboole_0))
% 0.48/0.68                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.48/0.68      inference('demod', [status(thm)], ['57', '58', '64'])).
% 0.48/0.68  thf('66', plain,
% 0.48/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('67', plain,
% 0.48/0.68      (![X18 : $i, X19 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.48/0.68          | ((k1_tops_1 @ X19 @ X18) != (k1_xboole_0))
% 0.48/0.68          | (v2_tops_1 @ X18 @ X19)
% 0.48/0.68          | ~ (l1_pre_topc @ X19))),
% 0.48/0.68      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.48/0.68  thf('68', plain,
% 0.48/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.48/0.68        | (v2_tops_1 @ sk_B @ sk_A)
% 0.48/0.68        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['66', '67'])).
% 0.48/0.68  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('70', plain,
% 0.48/0.68      (((v2_tops_1 @ sk_B @ sk_A)
% 0.48/0.68        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['68', '69'])).
% 0.48/0.68  thf('71', plain,
% 0.48/0.68      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.48/0.68         <= ((![X20 : $i]:
% 0.48/0.68                (((X20) = (k1_xboole_0))
% 0.48/0.68                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['65', '70'])).
% 0.48/0.68  thf('72', plain,
% 0.48/0.68      (((v2_tops_1 @ sk_B @ sk_A))
% 0.48/0.68         <= ((![X20 : $i]:
% 0.48/0.68                (((X20) = (k1_xboole_0))
% 0.48/0.68                 | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68                 | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68                 | ~ (r1_tarski @ X20 @ sk_B))))),
% 0.48/0.68      inference('simplify', [status(thm)], ['71'])).
% 0.48/0.68  thf('73', plain,
% 0.48/0.68      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.48/0.68      inference('split', [status(esa)], ['2'])).
% 0.48/0.68  thf('74', plain,
% 0.48/0.68      (~
% 0.48/0.68       (![X20 : $i]:
% 0.48/0.68          (((X20) = (k1_xboole_0))
% 0.48/0.68           | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.48/0.68           | ~ (v3_pre_topc @ X20 @ sk_A)
% 0.48/0.68           | ~ (r1_tarski @ X20 @ sk_B))) | 
% 0.48/0.68       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['72', '73'])).
% 0.48/0.68  thf('75', plain, ($false),
% 0.48/0.68      inference('sat_resolution*', [status(thm)],
% 0.48/0.68                ['1', '3', '5', '7', '34', '35', '74'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

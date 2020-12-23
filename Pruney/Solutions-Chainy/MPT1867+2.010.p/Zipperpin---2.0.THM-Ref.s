%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z4Xt5iYyoi

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:27 EST 2020

% Result     : Theorem 0.63s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 204 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  532 (1415 expanded)
%              Number of equality atoms :   23 (  37 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('15',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_pre_topc @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v3_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('33',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
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

thf('34',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X27 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ X29 )
       != ( sk_C_1 @ X26 @ X27 ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X15 @ X14 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['36','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','25'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X26 @ X27 ) @ X26 )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('51',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('55',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','11'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','25'])).

thf('60',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46','60'])).

thf('62',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['12','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z4Xt5iYyoi
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.63/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.63/0.83  % Solved by: fo/fo7.sh
% 0.63/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.63/0.83  % done 646 iterations in 0.385s
% 0.63/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.63/0.83  % SZS output start Refutation
% 0.63/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.63/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.63/0.83  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.63/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.63/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.63/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.63/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.63/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.63/0.83  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.63/0.83  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.63/0.83  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.63/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.63/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.63/0.83  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.63/0.83  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.63/0.83  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.63/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.63/0.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.63/0.83  thf(t35_tex_2, conjecture,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.63/0.83       ( ![B:$i]:
% 0.63/0.83         ( ( ( v1_xboole_0 @ B ) & 
% 0.63/0.83             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.83           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.63/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.63/0.83    (~( ![A:$i]:
% 0.63/0.83        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.63/0.83            ( l1_pre_topc @ A ) ) =>
% 0.63/0.83          ( ![B:$i]:
% 0.63/0.83            ( ( ( v1_xboole_0 @ B ) & 
% 0.63/0.83                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.63/0.83              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.63/0.83    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.63/0.83  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.63/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.63/0.83  thf(t4_subset_1, axiom,
% 0.63/0.83    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.63/0.83  thf('2', plain,
% 0.63/0.83      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.63/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.63/0.83  thf(t3_subset, axiom,
% 0.63/0.83    (![A:$i,B:$i]:
% 0.63/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.63/0.83  thf('3', plain,
% 0.63/0.83      (![X18 : $i, X19 : $i]:
% 0.63/0.83         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.63/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.63/0.83  thf('4', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.63/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.63/0.83  thf(d3_tarski, axiom,
% 0.63/0.83    (![A:$i,B:$i]:
% 0.63/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.63/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.63/0.83  thf('5', plain,
% 0.63/0.83      (![X4 : $i, X6 : $i]:
% 0.63/0.83         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.63/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.63/0.83  thf(d1_xboole_0, axiom,
% 0.63/0.83    (![A:$i]:
% 0.63/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.63/0.83  thf('6', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.63/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.63/0.83  thf('7', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.63/0.83  thf(d10_xboole_0, axiom,
% 0.63/0.83    (![A:$i,B:$i]:
% 0.63/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.63/0.83  thf('8', plain,
% 0.63/0.83      (![X7 : $i, X9 : $i]:
% 0.63/0.83         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.63/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.63/0.83  thf('9', plain,
% 0.63/0.83      (![X0 : $i, X1 : $i]:
% 0.63/0.83         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.63/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.63/0.83  thf('10', plain,
% 0.63/0.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.63/0.83      inference('sup-', [status(thm)], ['4', '9'])).
% 0.63/0.83  thf('11', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.63/0.83      inference('sup-', [status(thm)], ['1', '10'])).
% 0.63/0.83  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.67/0.83      inference('demod', [status(thm)], ['0', '11'])).
% 0.67/0.83  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('14', plain,
% 0.67/0.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['4', '9'])).
% 0.67/0.83  thf('15', plain,
% 0.67/0.83      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.67/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.67/0.83  thf(cc1_tops_1, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.83       ( ![B:$i]:
% 0.67/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.83           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.67/0.83  thf('16', plain,
% 0.67/0.83      (![X24 : $i, X25 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.67/0.83          | (v3_pre_topc @ X24 @ X25)
% 0.67/0.83          | ~ (v1_xboole_0 @ X24)
% 0.67/0.83          | ~ (l1_pre_topc @ X25)
% 0.67/0.83          | ~ (v2_pre_topc @ X25))),
% 0.67/0.83      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.67/0.83  thf('17', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v2_pre_topc @ X0)
% 0.67/0.83          | ~ (l1_pre_topc @ X0)
% 0.67/0.83          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.83          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.67/0.83  thf('18', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('19', plain,
% 0.67/0.83      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.67/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.83  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.67/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.83  thf('21', plain,
% 0.67/0.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.67/0.83         (~ (r2_hidden @ X3 @ X4)
% 0.67/0.83          | (r2_hidden @ X3 @ X5)
% 0.67/0.83          | ~ (r1_tarski @ X4 @ X5))),
% 0.67/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.67/0.83  thf('22', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['20', '21'])).
% 0.67/0.83  thf('23', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ (sk_B @ k1_xboole_0) @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['19', '22'])).
% 0.67/0.83  thf('24', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.67/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.83  thf('25', plain,
% 0.67/0.83      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.67/0.83  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.83      inference('sup-', [status(thm)], ['18', '25'])).
% 0.67/0.83  thf('27', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v2_pre_topc @ X0)
% 0.67/0.83          | ~ (l1_pre_topc @ X0)
% 0.67/0.83          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.67/0.83      inference('demod', [status(thm)], ['17', '26'])).
% 0.67/0.83  thf('28', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         ((v3_pre_topc @ X0 @ X1)
% 0.67/0.83          | ~ (v1_xboole_0 @ X0)
% 0.67/0.83          | ~ (l1_pre_topc @ X1)
% 0.67/0.83          | ~ (v2_pre_topc @ X1))),
% 0.67/0.83      inference('sup+', [status(thm)], ['14', '27'])).
% 0.67/0.83  thf('29', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v2_pre_topc @ sk_A)
% 0.67/0.83          | ~ (v1_xboole_0 @ X0)
% 0.67/0.83          | (v3_pre_topc @ X0 @ sk_A))),
% 0.67/0.83      inference('sup-', [status(thm)], ['13', '28'])).
% 0.67/0.83  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('31', plain,
% 0.67/0.83      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v3_pre_topc @ X0 @ sk_A))),
% 0.67/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.67/0.83  thf('32', plain,
% 0.67/0.83      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.67/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.67/0.83  thf('33', plain,
% 0.67/0.83      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.67/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.67/0.83  thf(d5_tex_2, axiom,
% 0.67/0.83    (![A:$i]:
% 0.67/0.83     ( ( l1_pre_topc @ A ) =>
% 0.67/0.83       ( ![B:$i]:
% 0.67/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.83           ( ( v2_tex_2 @ B @ A ) <=>
% 0.67/0.83             ( ![C:$i]:
% 0.67/0.83               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.83                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.67/0.83                      ( ![D:$i]:
% 0.67/0.83                        ( ( m1_subset_1 @
% 0.67/0.83                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.83                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.67/0.83                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.67/0.83                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.83  thf('34', plain,
% 0.67/0.83      (![X26 : $i, X27 : $i, X29 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.67/0.83          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.67/0.83          | ~ (v3_pre_topc @ X29 @ X27)
% 0.67/0.83          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X26 @ X29)
% 0.67/0.83              != (sk_C_1 @ X26 @ X27))
% 0.67/0.83          | (v2_tex_2 @ X26 @ X27)
% 0.67/0.83          | ~ (l1_pre_topc @ X27))),
% 0.67/0.83      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.67/0.83  thf('35', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]:
% 0.67/0.83         (~ (l1_pre_topc @ X0)
% 0.67/0.83          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.67/0.83          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.67/0.83              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.67/0.83          | ~ (v3_pre_topc @ X1 @ X0)
% 0.67/0.83          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.67/0.83      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.83  thf('36', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.67/0.83          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 0.67/0.83              != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.67/0.83          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.67/0.83          | ~ (l1_pre_topc @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['32', '35'])).
% 0.67/0.83  thf('37', plain,
% 0.67/0.83      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.67/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.83  thf('38', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.67/0.83      inference('simplify', [status(thm)], ['37'])).
% 0.67/0.83  thf('39', plain,
% 0.67/0.83      (![X18 : $i, X20 : $i]:
% 0.67/0.83         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.67/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.83  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.67/0.83  thf(idempotence_k9_subset_1, axiom,
% 0.67/0.83    (![A:$i,B:$i,C:$i]:
% 0.67/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.83       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.67/0.83  thf('41', plain,
% 0.67/0.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.67/0.83         (((k9_subset_1 @ X15 @ X14 @ X14) = (X14))
% 0.67/0.83          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.67/0.83      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.67/0.83  thf('42', plain,
% 0.67/0.83      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.67/0.83      inference('sup-', [status(thm)], ['40', '41'])).
% 0.67/0.83  thf('43', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (v3_pre_topc @ k1_xboole_0 @ X0)
% 0.67/0.83          | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ X0))
% 0.67/0.83          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.67/0.83          | ~ (l1_pre_topc @ X0))),
% 0.67/0.83      inference('demod', [status(thm)], ['36', '42'])).
% 0.67/0.83  thf('44', plain,
% 0.67/0.83      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.67/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.83        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.67/0.83        | ((k1_xboole_0) != (sk_C_1 @ k1_xboole_0 @ sk_A)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['31', '43'])).
% 0.67/0.83  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.83      inference('sup-', [status(thm)], ['18', '25'])).
% 0.67/0.83  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('47', plain,
% 0.67/0.83      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.67/0.83      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.67/0.83  thf('48', plain,
% 0.67/0.83      (![X26 : $i, X27 : $i]:
% 0.67/0.83         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.67/0.83          | (r1_tarski @ (sk_C_1 @ X26 @ X27) @ X26)
% 0.67/0.83          | (v2_tex_2 @ X26 @ X27)
% 0.67/0.83          | ~ (l1_pre_topc @ X27))),
% 0.67/0.83      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.67/0.83  thf('49', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         (~ (l1_pre_topc @ X0)
% 0.67/0.83          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.67/0.83          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['47', '48'])).
% 0.67/0.83  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.67/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.67/0.83  thf('51', plain,
% 0.67/0.83      (![X7 : $i, X9 : $i]:
% 0.67/0.83         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.67/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.67/0.83  thf('52', plain,
% 0.67/0.83      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.67/0.83  thf('53', plain,
% 0.67/0.83      (![X0 : $i]:
% 0.67/0.83         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.67/0.83          | ~ (l1_pre_topc @ X0)
% 0.67/0.83          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.67/0.83      inference('sup-', [status(thm)], ['49', '52'])).
% 0.67/0.83  thf('54', plain,
% 0.67/0.83      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['4', '9'])).
% 0.67/0.83  thf('55', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.67/0.83      inference('demod', [status(thm)], ['0', '11'])).
% 0.67/0.83  thf('56', plain,
% 0.67/0.83      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.83  thf('57', plain,
% 0.67/0.83      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.67/0.83        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.83        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.67/0.83      inference('sup-', [status(thm)], ['53', '56'])).
% 0.67/0.83  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.83  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.83      inference('sup-', [status(thm)], ['18', '25'])).
% 0.67/0.83  thf('60', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.67/0.83      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.67/0.83  thf('61', plain,
% 0.67/0.83      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.67/0.83      inference('demod', [status(thm)], ['44', '45', '46', '60'])).
% 0.67/0.83  thf('62', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.67/0.83      inference('simplify', [status(thm)], ['61'])).
% 0.67/0.83  thf('63', plain, ($false), inference('demod', [status(thm)], ['12', '62'])).
% 0.67/0.83  
% 0.67/0.83  % SZS output end Refutation
% 0.67/0.83  
% 0.67/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

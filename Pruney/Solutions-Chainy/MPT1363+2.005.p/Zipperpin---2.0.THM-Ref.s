%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PWv9bLf0SV

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 (2293 expanded)
%              Number of leaves         :   30 ( 658 expanded)
%              Depth                    :   20
%              Number of atoms          : 1045 (33699 expanded)
%              Number of equality atoms :   38 ( 424 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t18_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v2_compts_1 @ B @ A )
                    & ( r1_tarski @ C @ B )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( v2_compts_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_compts_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X4 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X20 @ X18 ) @ X18 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( v2_compts_1 @ ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ( ( sk_D @ X20 @ X18 )
        = X20 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_C @ sk_A )
      | ( ( sk_D @ sk_C @ X0 )
        = sk_C )
      | ~ ( r1_tarski @ sk_C @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('39',plain,
    ( ( ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_C )
    | ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v2_compts_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_D @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_C ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('45',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(t34_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ( X16 != X14 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t34_tops_2])).

thf('47',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X17 @ X15 )
      | ( v4_pre_topc @ X14 @ X17 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v4_pre_topc @ X0 @ X1 )
      | ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) )
    | ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('54',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( ( v2_compts_1 @ B @ A )
              <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
            & ( ( v2_pre_topc @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_pre_topc @ X23 )
      | ( X22 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X23 @ X22 ) )
      | ~ ( v2_compts_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(t17_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_compts_1 @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v2_compts_1 @ B @ A ) ) ) ) )).

thf('66',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v2_compts_1 @ X24 @ X25 )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ~ ( v1_compts_1 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t17_compts_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,
    ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('73',plain,
    ( ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','41'])).

thf('75',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','75'])).

thf('77',plain,(
    v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','55','56'])).

thf('78',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('79',plain,(
    v4_pre_topc @ sk_C @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('81',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('82',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('83',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('84',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('88',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( X22 != k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X23 @ X22 ) )
      | ~ ( v2_compts_1 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('90',plain,(
    ! [X23: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X23 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X23 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('94',plain,(
    v2_compts_1 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['85','96'])).

thf('98',plain,
    ( ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('100',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','74'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['76','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PWv9bLf0SV
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:33:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 345 iterations in 0.114s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.56  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.20/0.56  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.20/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(t18_compts_1, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.56                   ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.56                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ![C:$i]:
% 0.20/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                  ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.56                      ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.56                    ( v2_compts_1 @ C @ A ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t18_compts_1])).
% 0.20/0.56  thf('0', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t29_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.56          | ((u1_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 0.20/0.56          | ~ (l1_pre_topc @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('4', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf(d3_struct_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X3 : $i]:
% 0.20/0.56         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.20/0.56        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_k1_pre_topc, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.56       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.20/0.56         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X4 : $i, X5 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X4)
% 0.20/0.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.56          | (m1_pre_topc @ (k1_pre_topc @ X4 @ X5) @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('11', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf(dt_m1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X7 : $i, X8 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.56  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('15', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf(dt_l1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.56  thf('16', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.56  thf('17', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.56  thf('18', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t11_compts_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 0.20/0.56                 ( ( v2_compts_1 @ C @ A ) <=>
% 0.20/0.56                   ( ![D:$i]:
% 0.20/0.56                     ( ( m1_subset_1 @
% 0.20/0.56                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.56                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.56          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 0.20/0.56          | ~ (v2_compts_1 @ (sk_D @ X20 @ X18) @ X18)
% 0.20/0.56          | (v2_compts_1 @ X20 @ X19)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.56          | ~ (l1_pre_topc @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | (v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.56          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.20/0.56          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.56  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.56          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 0.20/0.56          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.20/0.56        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.56        | ~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.56             (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.56  thf('25', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('26', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      ((~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.56           (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.56  thf('28', plain, (~ (v2_compts_1 @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.56          (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['6', '17'])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('32', plain,
% 0.20/0.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.56          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 0.20/0.56          | ((sk_D @ X20 @ X18) = (X20))
% 0.20/0.56          | (v2_compts_1 @ X20 @ X19)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.56          | ~ (l1_pre_topc @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [t11_compts_1])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | (v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.56          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.20/0.56          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v2_compts_1 @ sk_C @ sk_A)
% 0.20/0.56          | ((sk_D @ sk_C @ X0) = (sk_C))
% 0.20/0.56          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 0.20/0.56          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((~ (r1_tarski @ sk_C @ sk_B)
% 0.20/0.56        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.56        | ((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))
% 0.20/0.56        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['30', '35'])).
% 0.20/0.56  thf('37', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('38', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      ((((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))
% 0.20/0.56        | (v2_compts_1 @ sk_C @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.56  thf('40', plain, (~ (v2_compts_1 @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('41', plain, (((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))),
% 0.20/0.56      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.56  thf('42', plain, (~ (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '41'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('44', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf('45', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf(t34_tops_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.56               ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.56                 ( ![D:$i]:
% 0.20/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.56                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.56          | ~ (v4_pre_topc @ X14 @ X15)
% 0.20/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.56          | (v4_pre_topc @ X16 @ X17)
% 0.20/0.56          | ((X16) != (X14))
% 0.20/0.56          | ~ (m1_pre_topc @ X17 @ X15)
% 0.20/0.56          | ~ (l1_pre_topc @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t34_tops_2])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X15)
% 0.20/0.56          | ~ (m1_pre_topc @ X17 @ X15)
% 0.20/0.56          | (v4_pre_topc @ X14 @ X17)
% 0.20/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.56          | ~ (v4_pre_topc @ X14 @ X15)
% 0.20/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ X1)
% 0.20/0.56          | (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X1)
% 0.20/0.56          | ~ (l1_pre_topc @ X1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '47'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['44', '48'])).
% 0.20/0.56  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.56        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 0.20/0.56        | (v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['43', '51'])).
% 0.20/0.56  thf('53', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t3_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.56  thf('54', plain,
% 0.20/0.56      (![X0 : $i, X2 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.56  thf('55', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.56  thf('56', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('57', plain, ((v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '55', '56'])).
% 0.20/0.56  thf('58', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(t12_compts_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56               ( ( v2_compts_1 @ B @ A ) <=>
% 0.20/0.56                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 0.20/0.56             ( ( v2_pre_topc @ A ) =>
% 0.20/0.56               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.56                 ( ( v2_compts_1 @ B @ A ) <=>
% 0.20/0.56                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.56          | ~ (v2_pre_topc @ X23)
% 0.20/0.56          | ((X22) = (k1_xboole_0))
% 0.20/0.56          | (v1_compts_1 @ (k1_pre_topc @ X23 @ X22))
% 0.20/0.56          | ~ (v2_compts_1 @ X22 @ X23)
% 0.20/0.56          | ~ (l1_pre_topc @ X23))),
% 0.20/0.56      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.20/0.56        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | ((sk_B) = (k1_xboole_0))
% 0.20/0.56        | ~ (v2_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.56  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('62', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('63', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.20/0.56  thf('65', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf(t17_compts_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( ( v1_compts_1 @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.56             ( v2_compts_1 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('66', plain,
% 0.20/0.56      (![X24 : $i, X25 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.56          | (v2_compts_1 @ X24 @ X25)
% 0.20/0.56          | ~ (v4_pre_topc @ X24 @ X25)
% 0.20/0.56          | ~ (v1_compts_1 @ X25)
% 0.20/0.56          | ~ (l1_pre_topc @ X25))),
% 0.20/0.56      inference('cnf', [status(esa)], [t17_compts_1])).
% 0.20/0.56  thf('67', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.56          | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.56  thf('68', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('69', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.56          | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.56  thf('70', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((sk_B) = (k1_xboole_0))
% 0.20/0.56          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['64', '69'])).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.56        | (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['57', '70'])).
% 0.20/0.56  thf('72', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.56  thf('73', plain,
% 0.20/0.56      (((v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56        | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.56  thf('74', plain, (~ (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['29', '41'])).
% 0.20/0.56  thf('75', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      (~ (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['42', '75'])).
% 0.20/0.56  thf('77', plain, ((v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '55', '56'])).
% 0.20/0.56  thf('78', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('79', plain, ((v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['77', '78'])).
% 0.20/0.56  thf('80', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 0.20/0.56          | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.56          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.20/0.56      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.56  thf('81', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('82', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('83', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('84', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.56          | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.56          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.20/0.56  thf('86', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('87', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('88', plain,
% 0.20/0.56      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.56  thf('89', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.56          | ((X22) != (k1_xboole_0))
% 0.20/0.56          | (v1_compts_1 @ (k1_pre_topc @ X23 @ X22))
% 0.20/0.56          | ~ (v2_compts_1 @ X22 @ X23)
% 0.20/0.56          | ~ (l1_pre_topc @ X23))),
% 0.20/0.56      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.56  thf('90', plain,
% 0.20/0.56      (![X23 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X23)
% 0.20/0.56          | ~ (v2_compts_1 @ k1_xboole_0 @ X23)
% 0.20/0.56          | (v1_compts_1 @ (k1_pre_topc @ X23 @ k1_xboole_0))
% 0.20/0.56          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.20/0.56      inference('simplify', [status(thm)], ['89'])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.56        | ~ (v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['88', '90'])).
% 0.20/0.56  thf('92', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('93', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('94', plain, ((v2_compts_1 @ k1_xboole_0 @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['92', '93'])).
% 0.20/0.56  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('96', plain, ((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['91', '94', '95'])).
% 0.20/0.56  thf('97', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.56          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.56          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['85', '96'])).
% 0.20/0.56  thf('98', plain,
% 0.20/0.56      (((v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.56        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['79', '97'])).
% 0.20/0.56  thf('99', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.56  thf('100', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.56      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.56  thf('101', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['99', '100'])).
% 0.20/0.56  thf('102', plain,
% 0.20/0.56      ((v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ k1_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['98', '101'])).
% 0.20/0.56  thf('103', plain, ($false), inference('demod', [status(thm)], ['76', '102'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

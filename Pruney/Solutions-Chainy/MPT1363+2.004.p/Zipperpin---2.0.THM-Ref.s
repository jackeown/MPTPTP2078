%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0lotaGWaJK

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:35 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 363 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  980 (4832 expanded)
%              Number of equality atoms :   26 (  60 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
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
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X8 ) @ X7 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
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
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ ( k2_struct_0 @ X22 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X24 @ X22 ) @ X22 )
      | ( v2_compts_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ ( k2_struct_0 @ X22 ) )
      | ( ( sk_D @ X24 @ X22 )
        = X24 )
      | ( v2_compts_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ( X19 != X17 )
      | ~ ( m1_pre_topc @ X20 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_tops_2])).

thf('47',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X20 @ X18 )
      | ( v4_pre_topc @ X17 @ X20 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
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
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
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

thf('58',plain,
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

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_compts_1 @ X26 @ X27 )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ~ ( v1_compts_1 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t17_compts_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('62',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf(t10_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf('63',plain,(
    ! [X21: $i] :
      ( ~ ( v2_compts_1 @ ( k2_struct_0 @ X21 ) @ X21 )
      | ( v1_compts_1 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('64',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('66',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ ( k2_struct_0 @ X22 ) )
      | ~ ( v2_compts_1 @ X24 @ X23 )
      | ( X25 != X24 )
      | ( v2_compts_1 @ X25 @ X22 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('70',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_compts_1 @ X24 @ X22 )
      | ~ ( v2_compts_1 @ X24 @ X23 )
      | ~ ( r1_tarski @ X24 @ ( k2_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('79',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf('81',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('82',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('83',plain,(
    v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','79','80','81','82'])).

thf('84',plain,(
    v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v4_pre_topc @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ X0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['60','61','84'])).

thf('86',plain,
    ( ( v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('88',plain,(
    v2_compts_1 @ sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['42','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0lotaGWaJK
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:59:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.06/1.24  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.24  % Solved by: fo/fo7.sh
% 1.06/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.24  % done 837 iterations in 0.745s
% 1.06/1.24  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.24  % SZS output start Refutation
% 1.06/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.24  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.06/1.24  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 1.06/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.24  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.06/1.24  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.24  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.24  thf(sk_C_type, type, sk_C: $i).
% 1.06/1.24  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 1.06/1.24  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.24  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.24  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.06/1.24  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.06/1.24  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.06/1.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.24  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 1.06/1.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.24  thf(t18_compts_1, conjecture,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ![C:$i]:
% 1.06/1.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 1.06/1.24                   ( v4_pre_topc @ C @ A ) ) =>
% 1.06/1.24                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 1.06/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.24    (~( ![A:$i]:
% 1.06/1.24        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.24          ( ![B:$i]:
% 1.06/1.24            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24              ( ![C:$i]:
% 1.06/1.24                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24                  ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 1.06/1.24                      ( v4_pre_topc @ C @ A ) ) =>
% 1.06/1.24                    ( v2_compts_1 @ C @ A ) ) ) ) ) ) ) )),
% 1.06/1.24    inference('cnf.neg', [status(esa)], [t18_compts_1])).
% 1.06/1.24  thf('0', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t29_pre_topc, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 1.06/1.24  thf('1', plain,
% 1.06/1.24      (![X12 : $i, X13 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 1.06/1.24          | ((u1_struct_0 @ (k1_pre_topc @ X13 @ X12)) = (X12))
% 1.06/1.24          | ~ (l1_pre_topc @ X13))),
% 1.06/1.24      inference('cnf', [status(esa)], [t29_pre_topc])).
% 1.06/1.24  thf('2', plain,
% 1.06/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.24        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['0', '1'])).
% 1.06/1.24  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('4', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['2', '3'])).
% 1.06/1.24  thf(d3_struct_0, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.06/1.24  thf('5', plain,
% 1.06/1.24      (![X6 : $i]:
% 1.06/1.24         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 1.06/1.24      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.06/1.24  thf('6', plain,
% 1.06/1.24      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 1.06/1.24        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.24      inference('sup+', [status(thm)], ['4', '5'])).
% 1.06/1.24  thf('7', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(dt_k1_pre_topc, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( ( l1_pre_topc @ A ) & 
% 1.06/1.24         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.24       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 1.06/1.24         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 1.06/1.24  thf('8', plain,
% 1.06/1.24      (![X7 : $i, X8 : $i]:
% 1.06/1.24         (~ (l1_pre_topc @ X7)
% 1.06/1.24          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 1.06/1.24          | (m1_pre_topc @ (k1_pre_topc @ X7 @ X8) @ X7))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 1.06/1.24  thf('9', plain,
% 1.06/1.24      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.06/1.24        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.24  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('11', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.24      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.24  thf(dt_m1_pre_topc, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.06/1.24  thf('12', plain,
% 1.06/1.24      (![X10 : $i, X11 : $i]:
% 1.06/1.24         (~ (m1_pre_topc @ X10 @ X11)
% 1.06/1.24          | (l1_pre_topc @ X10)
% 1.06/1.24          | ~ (l1_pre_topc @ X11))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.06/1.24  thf('13', plain,
% 1.06/1.24      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['11', '12'])).
% 1.06/1.24  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('15', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['13', '14'])).
% 1.06/1.24  thf(dt_l1_pre_topc, axiom,
% 1.06/1.24    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.06/1.24  thf('16', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 1.06/1.24      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.24  thf('17', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.24  thf('18', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['6', '17'])).
% 1.06/1.24  thf('19', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t11_compts_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_pre_topc @ B @ A ) =>
% 1.06/1.24           ( ![C:$i]:
% 1.06/1.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 1.06/1.24                 ( ( v2_compts_1 @ C @ A ) <=>
% 1.06/1.24                   ( ![D:$i]:
% 1.06/1.24                     ( ( m1_subset_1 @
% 1.06/1.24                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.06/1.24                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.24  thf('20', plain,
% 1.06/1.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.06/1.24         (~ (m1_pre_topc @ X22 @ X23)
% 1.06/1.24          | ~ (r1_tarski @ X24 @ (k2_struct_0 @ X22))
% 1.06/1.24          | ~ (v2_compts_1 @ (sk_D @ X24 @ X22) @ X22)
% 1.06/1.24          | (v2_compts_1 @ X24 @ X23)
% 1.06/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.06/1.24          | ~ (l1_pre_topc @ X23))),
% 1.06/1.24      inference('cnf', [status(esa)], [t11_compts_1])).
% 1.06/1.24  thf('21', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (l1_pre_topc @ sk_A)
% 1.06/1.24          | (v2_compts_1 @ sk_C @ sk_A)
% 1.06/1.24          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 1.06/1.24          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 1.06/1.24          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['19', '20'])).
% 1.06/1.24  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('23', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((v2_compts_1 @ sk_C @ sk_A)
% 1.06/1.24          | ~ (v2_compts_1 @ (sk_D @ sk_C @ X0) @ X0)
% 1.06/1.24          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 1.06/1.24          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.06/1.24      inference('demod', [status(thm)], ['21', '22'])).
% 1.06/1.24  thf('24', plain,
% 1.06/1.24      ((~ (r1_tarski @ sk_C @ sk_B)
% 1.06/1.24        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.06/1.24        | ~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.06/1.24             (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24        | (v2_compts_1 @ sk_C @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['18', '23'])).
% 1.06/1.24  thf('25', plain, ((r1_tarski @ sk_C @ sk_B)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('26', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.24      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.24  thf('27', plain,
% 1.06/1.24      ((~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.06/1.24           (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24        | (v2_compts_1 @ sk_C @ sk_A))),
% 1.06/1.24      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.06/1.24  thf('28', plain, (~ (v2_compts_1 @ sk_C @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('29', plain,
% 1.06/1.24      (~ (v2_compts_1 @ (sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.06/1.24          (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('clc', [status(thm)], ['27', '28'])).
% 1.06/1.24  thf('30', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['6', '17'])).
% 1.06/1.24  thf('31', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('32', plain,
% 1.06/1.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.06/1.24         (~ (m1_pre_topc @ X22 @ X23)
% 1.06/1.24          | ~ (r1_tarski @ X24 @ (k2_struct_0 @ X22))
% 1.06/1.24          | ((sk_D @ X24 @ X22) = (X24))
% 1.06/1.24          | (v2_compts_1 @ X24 @ X23)
% 1.06/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.06/1.24          | ~ (l1_pre_topc @ X23))),
% 1.06/1.24      inference('cnf', [status(esa)], [t11_compts_1])).
% 1.06/1.24  thf('33', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (l1_pre_topc @ sk_A)
% 1.06/1.24          | (v2_compts_1 @ sk_C @ sk_A)
% 1.06/1.24          | ((sk_D @ sk_C @ X0) = (sk_C))
% 1.06/1.24          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 1.06/1.24          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['31', '32'])).
% 1.06/1.24  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('35', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((v2_compts_1 @ sk_C @ sk_A)
% 1.06/1.24          | ((sk_D @ sk_C @ X0) = (sk_C))
% 1.06/1.24          | ~ (r1_tarski @ sk_C @ (k2_struct_0 @ X0))
% 1.06/1.24          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 1.06/1.24      inference('demod', [status(thm)], ['33', '34'])).
% 1.06/1.24  thf('36', plain,
% 1.06/1.24      ((~ (r1_tarski @ sk_C @ sk_B)
% 1.06/1.24        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.06/1.24        | ((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))
% 1.06/1.24        | (v2_compts_1 @ sk_C @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['30', '35'])).
% 1.06/1.24  thf('37', plain, ((r1_tarski @ sk_C @ sk_B)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('38', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.24      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.24  thf('39', plain,
% 1.06/1.24      ((((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))
% 1.06/1.24        | (v2_compts_1 @ sk_C @ sk_A))),
% 1.06/1.24      inference('demod', [status(thm)], ['36', '37', '38'])).
% 1.06/1.24  thf('40', plain, (~ (v2_compts_1 @ sk_C @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('41', plain, (((sk_D @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_C))),
% 1.06/1.24      inference('clc', [status(thm)], ['39', '40'])).
% 1.06/1.24  thf('42', plain, (~ (v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['29', '41'])).
% 1.06/1.24  thf('43', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('44', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.24      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.24  thf('45', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['2', '3'])).
% 1.06/1.24  thf(t34_tops_2, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ![C:$i]:
% 1.06/1.24             ( ( m1_pre_topc @ C @ A ) =>
% 1.06/1.24               ( ( v4_pre_topc @ B @ A ) =>
% 1.06/1.24                 ( ![D:$i]:
% 1.06/1.24                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 1.06/1.24                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.24  thf('46', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.06/1.24          | ~ (v4_pre_topc @ X17 @ X18)
% 1.06/1.24          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.06/1.24          | (v4_pre_topc @ X19 @ X20)
% 1.06/1.24          | ((X19) != (X17))
% 1.06/1.24          | ~ (m1_pre_topc @ X20 @ X18)
% 1.06/1.24          | ~ (l1_pre_topc @ X18))),
% 1.06/1.24      inference('cnf', [status(esa)], [t34_tops_2])).
% 1.06/1.24  thf('47', plain,
% 1.06/1.24      (![X17 : $i, X18 : $i, X20 : $i]:
% 1.06/1.24         (~ (l1_pre_topc @ X18)
% 1.06/1.24          | ~ (m1_pre_topc @ X20 @ X18)
% 1.06/1.24          | (v4_pre_topc @ X17 @ X20)
% 1.06/1.24          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.06/1.24          | ~ (v4_pre_topc @ X17 @ X18)
% 1.06/1.24          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.06/1.24      inference('simplify', [status(thm)], ['46'])).
% 1.06/1.24  thf('48', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 1.06/1.24          | ~ (v4_pre_topc @ X0 @ X1)
% 1.06/1.24          | (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X1)
% 1.06/1.24          | ~ (l1_pre_topc @ X1))),
% 1.06/1.24      inference('sup-', [status(thm)], ['45', '47'])).
% 1.06/1.24  thf('49', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (l1_pre_topc @ sk_A)
% 1.06/1.24          | (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24          | ~ (v4_pre_topc @ X0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['44', '48'])).
% 1.06/1.24  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('51', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         ((v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24          | ~ (v4_pre_topc @ X0 @ sk_A)
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.24          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['49', '50'])).
% 1.06/1.24  thf('52', plain,
% 1.06/1.24      ((~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))
% 1.06/1.24        | ~ (v4_pre_topc @ sk_C @ sk_A)
% 1.06/1.24        | (v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['43', '51'])).
% 1.06/1.24  thf('53', plain, ((r1_tarski @ sk_C @ sk_B)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf(t3_subset, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.24  thf('54', plain,
% 1.06/1.24      (![X3 : $i, X5 : $i]:
% 1.06/1.24         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 1.06/1.24      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.24  thf('55', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 1.06/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.06/1.24  thf('56', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('57', plain, ((v4_pre_topc @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['52', '55', '56'])).
% 1.06/1.24  thf('58', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['2', '3'])).
% 1.06/1.24  thf(t17_compts_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ![B:$i]:
% 1.06/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.24           ( ( ( v1_compts_1 @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 1.06/1.24             ( v2_compts_1 @ B @ A ) ) ) ) ))).
% 1.06/1.24  thf('59', plain,
% 1.06/1.24      (![X26 : $i, X27 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.06/1.24          | (v2_compts_1 @ X26 @ X27)
% 1.06/1.24          | ~ (v4_pre_topc @ X26 @ X27)
% 1.06/1.24          | ~ (v1_compts_1 @ X27)
% 1.06/1.24          | ~ (l1_pre_topc @ X27))),
% 1.06/1.24      inference('cnf', [status(esa)], [t17_compts_1])).
% 1.06/1.24  thf('60', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 1.06/1.24          | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24          | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['58', '59'])).
% 1.06/1.24  thf('61', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['13', '14'])).
% 1.06/1.24  thf('62', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['6', '17'])).
% 1.06/1.24  thf(t10_compts_1, axiom,
% 1.06/1.24    (![A:$i]:
% 1.06/1.24     ( ( l1_pre_topc @ A ) =>
% 1.06/1.24       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 1.06/1.24  thf('63', plain,
% 1.06/1.24      (![X21 : $i]:
% 1.06/1.24         (~ (v2_compts_1 @ (k2_struct_0 @ X21) @ X21)
% 1.06/1.24          | (v1_compts_1 @ X21)
% 1.06/1.24          | ~ (l1_pre_topc @ X21))),
% 1.06/1.24      inference('cnf', [status(esa)], [t10_compts_1])).
% 1.06/1.24  thf('64', plain,
% 1.06/1.24      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['62', '63'])).
% 1.06/1.24  thf('65', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['13', '14'])).
% 1.06/1.24  thf('66', plain,
% 1.06/1.24      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['64', '65'])).
% 1.06/1.24  thf('67', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['2', '3'])).
% 1.06/1.24  thf('68', plain,
% 1.06/1.24      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('69', plain,
% 1.06/1.24      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.24         (~ (m1_pre_topc @ X22 @ X23)
% 1.06/1.24          | ~ (r1_tarski @ X24 @ (k2_struct_0 @ X22))
% 1.06/1.24          | ~ (v2_compts_1 @ X24 @ X23)
% 1.06/1.24          | ((X25) != (X24))
% 1.06/1.24          | (v2_compts_1 @ X25 @ X22)
% 1.06/1.24          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.06/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.06/1.24          | ~ (l1_pre_topc @ X23))),
% 1.06/1.24      inference('cnf', [status(esa)], [t11_compts_1])).
% 1.06/1.24  thf('70', plain,
% 1.06/1.24      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.06/1.24         (~ (l1_pre_topc @ X23)
% 1.06/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.06/1.24          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.06/1.24          | (v2_compts_1 @ X24 @ X22)
% 1.06/1.24          | ~ (v2_compts_1 @ X24 @ X23)
% 1.06/1.24          | ~ (r1_tarski @ X24 @ (k2_struct_0 @ X22))
% 1.06/1.24          | ~ (m1_pre_topc @ X22 @ X23))),
% 1.06/1.24      inference('simplify', [status(thm)], ['69'])).
% 1.06/1.24  thf('71', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.24          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.06/1.24          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 1.06/1.24          | (v2_compts_1 @ sk_B @ X0)
% 1.06/1.24          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.06/1.24          | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['68', '70'])).
% 1.06/1.24  thf('72', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.24  thf('74', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (m1_pre_topc @ X0 @ sk_A)
% 1.06/1.24          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 1.06/1.24          | (v2_compts_1 @ sk_B @ X0)
% 1.06/1.24          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 1.06/1.24      inference('demod', [status(thm)], ['71', '72', '73'])).
% 1.06/1.24  thf('75', plain,
% 1.06/1.24      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 1.06/1.24        | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24        | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.06/1.24        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 1.06/1.24      inference('sup-', [status(thm)], ['67', '74'])).
% 1.06/1.24  thf(d10_xboole_0, axiom,
% 1.06/1.24    (![A:$i,B:$i]:
% 1.06/1.24     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.24  thf('76', plain,
% 1.06/1.24      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.06/1.24      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.24  thf('77', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.06/1.24      inference('simplify', [status(thm)], ['76'])).
% 1.06/1.24  thf('78', plain,
% 1.06/1.24      (![X3 : $i, X5 : $i]:
% 1.06/1.24         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 1.06/1.24      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.24  thf('79', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.24      inference('sup-', [status(thm)], ['77', '78'])).
% 1.06/1.24  thf('80', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['6', '17'])).
% 1.06/1.24  thf('81', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.06/1.24      inference('simplify', [status(thm)], ['76'])).
% 1.06/1.24  thf('82', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.24      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.24  thf('83', plain, ((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['75', '79', '80', '81', '82'])).
% 1.06/1.24  thf('84', plain, ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['66', '83'])).
% 1.06/1.24  thf('85', plain,
% 1.06/1.24      (![X0 : $i]:
% 1.06/1.24         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B))
% 1.06/1.24          | ~ (v4_pre_topc @ X0 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24          | (v2_compts_1 @ X0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.24      inference('demod', [status(thm)], ['60', '61', '84'])).
% 1.06/1.24  thf('86', plain,
% 1.06/1.24      (((v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))
% 1.06/1.24        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B)))),
% 1.06/1.24      inference('sup-', [status(thm)], ['57', '85'])).
% 1.06/1.24  thf('87', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 1.06/1.24      inference('sup-', [status(thm)], ['53', '54'])).
% 1.06/1.24  thf('88', plain, ((v2_compts_1 @ sk_C @ (k1_pre_topc @ sk_A @ sk_B))),
% 1.06/1.24      inference('demod', [status(thm)], ['86', '87'])).
% 1.06/1.24  thf('89', plain, ($false), inference('demod', [status(thm)], ['42', '88'])).
% 1.06/1.24  
% 1.06/1.24  % SZS output end Refutation
% 1.06/1.24  
% 1.08/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

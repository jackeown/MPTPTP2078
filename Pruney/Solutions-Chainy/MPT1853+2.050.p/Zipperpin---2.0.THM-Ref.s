%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z4uJUqYIrX

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 727 expanded)
%              Number of leaves         :   18 ( 202 expanded)
%              Depth                    :   20
%              Number of atoms          :  876 (10082 expanded)
%              Number of equality atoms :   17 (  96 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('7',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('18',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ( X4
       != ( k1_tex_2 @ X3 @ X2 ) )
      | ( ( u1_struct_0 @ X4 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X3 ) @ X2 ) )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( v1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X3 @ X2 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X3 @ X2 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X3 @ X2 ) @ X3 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X3 @ X2 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X3 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf('30',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('33',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','40'])).

thf('42',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ~ ( v1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( v1_tex_2 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tex_2 @ X7 @ X8 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf('51',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','51'])).

thf('53',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','54'])).

thf('56',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','40'])).

thf('58',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( X9
       != ( u1_struct_0 @ X7 ) )
      | ~ ( v1_tex_2 @ X7 @ X8 )
      | ( v1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_tex_2 @ X7 @ X8 )
      | ~ ( m1_pre_topc @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ X0 )
      | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('67',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('68',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','54','67'])).

thf('69',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf('71',plain,(
    v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['56','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z4uJUqYIrX
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 36 iterations in 0.024s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.22/0.49  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(t20_tex_2, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.49             ( v1_subset_1 @
% 0.22/0.49               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.49                ( v1_subset_1 @
% 0.22/0.49                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.49                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49           (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49           (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~
% 0.22/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49               (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49         (u1_struct_0 @ sk_A))) | 
% 0.22/0.49       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49         (u1_struct_0 @ sk_A))
% 0.22/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49         (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49               (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k1_tex_2, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.22/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.22/0.49         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X5)
% 0.22/0.49          | (v2_struct_0 @ X5)
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.49          | (m1_pre_topc @ (k1_tex_2 @ X5 @ X6) @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.49        | (v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('11', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf(t1_tsep_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( m1_subset_1 @
% 0.22/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X0 @ X1)
% 0.22/0.49          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.49          | ~ (l1_pre_topc @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf('16', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X5)
% 0.22/0.49          | (v2_struct_0 @ X5)
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.49          | (v1_pre_topc @ (k1_tex_2 @ X5 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49        | (v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf(d4_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.22/0.49                 ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.49               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.22/0.49                 ( ( u1_struct_0 @ C ) =
% 0.22/0.49                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3))
% 0.22/0.49          | ((X4) != (k1_tex_2 @ X3 @ X2))
% 0.22/0.49          | ((u1_struct_0 @ X4) = (k6_domain_1 @ (u1_struct_0 @ X3) @ X2))
% 0.22/0.49          | ~ (m1_pre_topc @ X4 @ X3)
% 0.22/0.49          | ~ (v1_pre_topc @ X4)
% 0.22/0.49          | (v2_struct_0 @ X4)
% 0.22/0.49          | ~ (l1_pre_topc @ X3)
% 0.22/0.49          | (v2_struct_0 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         ((v2_struct_0 @ X3)
% 0.22/0.49          | ~ (l1_pre_topc @ X3)
% 0.22/0.49          | (v2_struct_0 @ (k1_tex_2 @ X3 @ X2))
% 0.22/0.49          | ~ (v1_pre_topc @ (k1_tex_2 @ X3 @ X2))
% 0.22/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ X3 @ X2) @ X3)
% 0.22/0.49          | ((u1_struct_0 @ (k1_tex_2 @ X3 @ X2))
% 0.22/0.49              = (k6_domain_1 @ (u1_struct_0 @ X3) @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X3)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.49        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.49        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '24'])).
% 0.22/0.49  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.49        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.49  thf('29', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.22/0.49        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49        | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X5)
% 0.22/0.49          | (v2_struct_0 @ X5)
% 0.22/0.49          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.22/0.49          | ~ (v2_struct_0 @ (k1_tex_2 @ X5 @ X6)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49        | (v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.49  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      (((v2_struct_0 @ sk_A)
% 0.22/0.49        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.22/0.49      inference('clc', [status(thm)], ['30', '37'])).
% 0.22/0.49  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf(t13_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.49                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.22/0.49                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.49          | ((X9) != (u1_struct_0 @ X7))
% 0.22/0.49          | ~ (v1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.22/0.49          | (v1_tex_2 @ X7 @ X8)
% 0.22/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.49          | ~ (l1_pre_topc @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X8)
% 0.22/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.22/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.49          | (v1_tex_2 @ X7 @ X8)
% 0.22/0.49          | ~ (v1_subset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X8))
% 0.22/0.49          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.22/0.49      inference('simplify', [status(thm)], ['43'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.49               (u1_struct_0 @ X0))
% 0.22/0.49          | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['42', '44'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49               (u1_struct_0 @ X0))
% 0.22/0.49          | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.49        | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49             (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '47'])).
% 0.22/0.49  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('50', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.49        | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49             (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.49         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49               (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '51'])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('54', plain,
% 0.22/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) | 
% 0.22/0.49       ~
% 0.22/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49         (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49         (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '54'])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49          (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['15', '40'])).
% 0.22/0.49  thf('58', plain,
% 0.22/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.49          | ((X9) != (u1_struct_0 @ X7))
% 0.22/0.49          | ~ (v1_tex_2 @ X7 @ X8)
% 0.22/0.49          | (v1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.22/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.49          | ~ (l1_pre_topc @ X8))),
% 0.22/0.49      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X8)
% 0.22/0.49          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.22/0.49               (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.49          | (v1_subset_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X8))
% 0.22/0.49          | ~ (v1_tex_2 @ X7 @ X8)
% 0.22/0.49          | ~ (m1_pre_topc @ X7 @ X8))),
% 0.22/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.49             (u1_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['58', '60'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.49          | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ X0)
% 0.22/0.49          | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49             (u1_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_pre_topc @ X0))),
% 0.22/0.49      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.49        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49           (u1_struct_0 @ sk_A))
% 0.22/0.49        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.49        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['57', '63'])).
% 0.22/0.49  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.49         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) | 
% 0.22/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49         (u1_struct_0 @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('68', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['2', '54', '67'])).
% 0.22/0.49  thf('69', plain, ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.22/0.49  thf('70', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.49      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('71', plain,
% 0.22/0.49      ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49        (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['64', '65', '69', '70'])).
% 0.22/0.49  thf('72', plain, ($false), inference('demod', [status(thm)], ['56', '71'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

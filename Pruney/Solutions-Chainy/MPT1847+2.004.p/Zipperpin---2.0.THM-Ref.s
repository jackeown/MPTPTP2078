%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SRHC612cAb

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:54 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  269 (2283 expanded)
%              Number of leaves         :   41 ( 678 expanded)
%              Depth                    :   24
%              Number of atoms          : 2010 (27518 expanded)
%              Number of equality atoms :   86 (1033 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t14_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                  & ( v1_tex_2 @ B @ A ) )
               => ( v1_tex_2 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                    & ( v1_tex_2 @ B @ A ) )
                 => ( v1_tex_2 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tex_2])).

thf('1',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( v1_tex_2 @ X31 @ X32 )
      | ( X33
       != ( u1_struct_0 @ X31 ) )
      | ( v1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('17',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X31 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_tex_2 @ X31 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_tex_2 @ X0 @ X1 )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k1_pre_topc @ X7 @ X6 ) )
      | ( ( k2_struct_0 @ X8 )
        = X6 )
      | ~ ( m1_pre_topc @ X8 @ X7 )
      | ~ ( v1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('28',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('38',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('57',plain,
    ( ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('59',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('60',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('66',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_B ) ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['41','66'])).

thf('68',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('71',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','67','68','69','70'])).

thf('72',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('85',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','85'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('87',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('88',plain,
    ( ( v1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( ( sk_C_1 @ X31 @ X32 )
        = ( u1_struct_0 @ X31 ) )
      | ( v1_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ( ( sk_C_1 @ sk_C_2 @ sk_A )
      = ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','85'])).

thf('94',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('95',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) )
      = ( k2_struct_0 @ sk_C_2 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('98',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('99',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) )
    | ~ ( l1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('104',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) )
      = ( k2_struct_0 @ sk_C_2 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['95','104','105'])).

thf('107',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','85'])).

thf('108',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('109',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) @ sk_A ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) )
    = ( k2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('116',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('118',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) )
      = ( u1_struct_0 @ sk_C_2 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('123',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('124',plain,
    ( ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) @ sk_A )
    | ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) )
      = ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('126',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('127',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) @ sk_A ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_2 ) ) )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['124','129'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) )
      = ( u1_struct_0 @ sk_C_2 ) )
    | ~ ( l1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['113','130'])).

thf('132',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('133',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_2 ) ) )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['112','133'])).

thf('135',plain,
    ( ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ( ( sk_C_1 @ sk_C_2 @ sk_A )
      = ( k2_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['91','92','134'])).

thf('136',plain,(
    ~ ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_A )
    = ( k2_struct_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ( v1_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('139',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    ~ ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ~ ( v1_subset_1 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','144'])).

thf('146',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['71','145'])).

thf('147',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('148',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('149',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('152',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('153',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('154',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('156',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','144'])).

thf('157',plain,
    ( ( ( k2_struct_0 @ sk_C_2 )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('159',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('161',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_C_2 ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_C_2 )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','159','160'])).

thf('162',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['112','133'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('163',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('164',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('165',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('168',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_pre_topc @ X28 @ X27 )
      | ( m1_pre_topc @ X28 @ ( g1_pre_topc @ ( u1_struct_0 @ X27 ) @ ( u1_pre_topc @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('172',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['170','174'])).

thf('176',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) )
    | ~ ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['162','175'])).

thf('177',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['112','133'])).

thf('178',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('179',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('180',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) )
    | ~ ( l1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('183',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
      = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['178','183'])).

thf('185',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('186',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['81','82'])).

thf('188',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['176','177','186','187'])).

thf('189',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['181','182'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('190',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ ( g1_pre_topc @ ( u1_struct_0 @ X26 ) @ ( u1_pre_topc @ X26 ) ) )
      | ( m1_pre_topc @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( k2_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) @ sk_B ),
    inference('sup-',[status(thm)],['188','195'])).

thf('197',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('198',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('200',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['112','133'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('202',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('203',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X6 ) @ X7 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['201','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('208',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['206','209'])).

thf('211',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) )
      = ( u1_struct_0 @ sk_C_2 ) )
    | ~ ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['200','210'])).

thf('212',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['112','133'])).

thf('213',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['81','82'])).

thf('214',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) )
    = ( k2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf('215',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['112','133'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('217',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) )
    | ~ ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['81','82'])).

thf('219',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_2 @ ( k2_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_2 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['198','199','214','219'])).

thf('221',plain,
    ( ( k2_struct_0 @ sk_C_2 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','220'])).

thf('222',plain,(
    v1_subset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['146','221'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('223',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X5 ) @ X5 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf('224',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('225',plain,(
    ! [X5: $i] :
      ~ ( v1_subset_1 @ X5 @ X5 ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    $false ),
    inference('sup-',[status(thm)],['222','225'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SRHC612cAb
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.71/0.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.87  % Solved by: fo/fo7.sh
% 0.71/0.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.87  % done 637 iterations in 0.415s
% 0.71/0.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.87  % SZS output start Refutation
% 0.71/0.87  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.71/0.87  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.71/0.87  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.87  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.71/0.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.87  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.71/0.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.71/0.87  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.71/0.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.87  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.71/0.87  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.71/0.87  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.71/0.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.87  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.71/0.87  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.71/0.87  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.71/0.87  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.87  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.71/0.87  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.71/0.87  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.71/0.87  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.71/0.87  thf(d3_struct_0, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.71/0.87  thf('0', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf(t14_tex_2, conjecture,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( m1_pre_topc @ B @ A ) =>
% 0.71/0.87           ( ![C:$i]:
% 0.71/0.87             ( ( m1_pre_topc @ C @ A ) =>
% 0.71/0.87               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.71/0.87                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.71/0.87                   ( v1_tex_2 @ B @ A ) ) =>
% 0.71/0.87                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.71/0.87  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.87    (~( ![A:$i]:
% 0.71/0.87        ( ( l1_pre_topc @ A ) =>
% 0.71/0.87          ( ![B:$i]:
% 0.71/0.87            ( ( m1_pre_topc @ B @ A ) =>
% 0.71/0.87              ( ![C:$i]:
% 0.71/0.87                ( ( m1_pre_topc @ C @ A ) =>
% 0.71/0.87                  ( ( ( ( g1_pre_topc @
% 0.71/0.87                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.71/0.87                        ( g1_pre_topc @
% 0.71/0.87                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.71/0.87                      ( v1_tex_2 @ B @ A ) ) =>
% 0.71/0.87                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.71/0.87    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.71/0.87  thf('1', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(t1_tsep_1, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( m1_pre_topc @ B @ A ) =>
% 0.71/0.87           ( m1_subset_1 @
% 0.71/0.87             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.71/0.87  thf('2', plain,
% 0.71/0.87      (![X29 : $i, X30 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X29 @ X30)
% 0.71/0.87          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.71/0.87             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.71/0.87          | ~ (l1_pre_topc @ X30))),
% 0.71/0.87      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.71/0.87  thf('3', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.71/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.87      inference('sup-', [status(thm)], ['1', '2'])).
% 0.71/0.87  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('5', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['3', '4'])).
% 0.71/0.87  thf('6', plain,
% 0.71/0.87      (((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.71/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_B))),
% 0.71/0.87      inference('sup+', [status(thm)], ['0', '5'])).
% 0.71/0.87  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(dt_m1_pre_topc, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.71/0.87  thf('8', plain,
% 0.71/0.87      (![X23 : $i, X24 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X23 @ X24)
% 0.71/0.87          | (l1_pre_topc @ X23)
% 0.71/0.87          | ~ (l1_pre_topc @ X24))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.71/0.87  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.71/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.71/0.87  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.71/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.87  thf(dt_l1_pre_topc, axiom,
% 0.71/0.87    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.71/0.87  thf('12', plain,
% 0.71/0.87      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.71/0.87  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.71/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.71/0.87  thf('14', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['6', '13'])).
% 0.71/0.87  thf('15', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf(d3_tex_2, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( m1_pre_topc @ B @ A ) =>
% 0.71/0.87           ( ( v1_tex_2 @ B @ A ) <=>
% 0.71/0.87             ( ![C:$i]:
% 0.71/0.87               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.87                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.71/0.87                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.71/0.87  thf('16', plain,
% 0.71/0.87      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X31 @ X32)
% 0.71/0.87          | ~ (v1_tex_2 @ X31 @ X32)
% 0.71/0.87          | ((X33) != (u1_struct_0 @ X31))
% 0.71/0.87          | (v1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 0.71/0.87          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.71/0.87          | ~ (l1_pre_topc @ X32))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.71/0.87  thf('17', plain,
% 0.71/0.87      (![X31 : $i, X32 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X32)
% 0.71/0.87          | ~ (m1_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.71/0.87               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.71/0.87          | (v1_subset_1 @ (u1_struct_0 @ X31) @ (u1_struct_0 @ X32))
% 0.71/0.87          | ~ (v1_tex_2 @ X31 @ X32)
% 0.71/0.87          | ~ (m1_pre_topc @ X31 @ X32))),
% 0.71/0.87      inference('simplify', [status(thm)], ['16'])).
% 0.71/0.87  thf('18', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         (~ (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.71/0.87             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.71/0.87          | ~ (l1_struct_0 @ X0)
% 0.71/0.87          | ~ (m1_pre_topc @ X0 @ X1)
% 0.71/0.87          | ~ (v1_tex_2 @ X0 @ X1)
% 0.71/0.87          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.71/0.87          | ~ (l1_pre_topc @ X1))),
% 0.71/0.87      inference('sup-', [status(thm)], ['15', '17'])).
% 0.71/0.87  thf('19', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.71/0.87        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.71/0.87        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.71/0.87        | ~ (l1_struct_0 @ sk_B))),
% 0.71/0.87      inference('sup-', [status(thm)], ['14', '18'])).
% 0.71/0.87  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('21', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['6', '13'])).
% 0.71/0.87  thf(d10_pre_topc, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.87           ( ![C:$i]:
% 0.71/0.87             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.71/0.87               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.71/0.87                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.71/0.87  thf('22', plain,
% 0.71/0.87      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.71/0.87         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.71/0.87          | ((X8) != (k1_pre_topc @ X7 @ X6))
% 0.71/0.87          | ((k2_struct_0 @ X8) = (X6))
% 0.71/0.87          | ~ (m1_pre_topc @ X8 @ X7)
% 0.71/0.87          | ~ (v1_pre_topc @ X8)
% 0.71/0.87          | ~ (l1_pre_topc @ X7))),
% 0.71/0.87      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.71/0.87  thf('23', plain,
% 0.71/0.87      (![X6 : $i, X7 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X7)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.71/0.87          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.71/0.87          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.71/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.71/0.87  thf('24', plain,
% 0.71/0.87      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.71/0.87          = (k2_struct_0 @ sk_B))
% 0.71/0.87        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)
% 0.71/0.87        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['21', '23'])).
% 0.71/0.87  thf('25', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('26', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['3', '4'])).
% 0.71/0.87  thf(dt_k1_pre_topc, axiom,
% 0.71/0.87    (![A:$i,B:$i]:
% 0.71/0.87     ( ( ( l1_pre_topc @ A ) & 
% 0.71/0.87         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.87       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.71/0.87         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.71/0.87  thf('27', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (v1_pre_topc @ (k1_pre_topc @ X20 @ X21)))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('28', plain,
% 0.71/0.87      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.87  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('30', plain,
% 0.71/0.87      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.71/0.87      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.87  thf('31', plain,
% 0.71/0.87      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_B))),
% 0.71/0.87      inference('sup+', [status(thm)], ['25', '30'])).
% 0.71/0.87  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.71/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.71/0.87  thf('33', plain,
% 0.71/0.87      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))),
% 0.71/0.87      inference('demod', [status(thm)], ['31', '32'])).
% 0.71/0.87  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('35', plain,
% 0.71/0.87      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.71/0.87          = (k2_struct_0 @ sk_B))
% 0.71/0.87        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['24', '33', '34'])).
% 0.71/0.87  thf('36', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['6', '13'])).
% 0.71/0.87  thf('37', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('38', plain,
% 0.71/0.87      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['36', '37'])).
% 0.71/0.87  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('40', plain,
% 0.71/0.87      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)) @ sk_A)),
% 0.71/0.87      inference('demod', [status(thm)], ['38', '39'])).
% 0.71/0.87  thf('41', plain,
% 0.71/0.87      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.71/0.87         = (k2_struct_0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['35', '40'])).
% 0.71/0.87  thf('42', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('43', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('44', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['3', '4'])).
% 0.71/0.87  thf('45', plain,
% 0.71/0.87      (((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.71/0.87         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.87      inference('sup+', [status(thm)], ['43', '44'])).
% 0.71/0.87  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('47', plain,
% 0.71/0.87      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.71/0.87  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.87  thf('49', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['45', '48'])).
% 0.71/0.87  thf('50', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('51', plain,
% 0.71/0.87      (![X6 : $i, X7 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X7)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.71/0.87          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.71/0.87          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.71/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.71/0.87  thf('52', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_struct_0 @ X0)
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.71/0.87          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['50', '51'])).
% 0.71/0.87  thf('53', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.71/0.87        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.71/0.87        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.71/0.87            = (u1_struct_0 @ sk_B))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['49', '52'])).
% 0.71/0.87  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('55', plain,
% 0.71/0.87      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))),
% 0.71/0.87      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.87  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.87  thf('57', plain,
% 0.71/0.87      ((~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.71/0.87        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.71/0.87            = (u1_struct_0 @ sk_B)))),
% 0.71/0.87      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.71/0.87  thf('58', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['3', '4'])).
% 0.71/0.87  thf('59', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('60', plain,
% 0.71/0.87      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['58', '59'])).
% 0.71/0.87  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('62', plain,
% 0.71/0.87      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)) @ sk_A)),
% 0.71/0.87      inference('demod', [status(thm)], ['60', '61'])).
% 0.71/0.87  thf('63', plain,
% 0.71/0.87      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_B)))
% 0.71/0.87         = (u1_struct_0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['57', '62'])).
% 0.71/0.87  thf('64', plain,
% 0.71/0.87      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.71/0.87          = (u1_struct_0 @ sk_B))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_B))),
% 0.71/0.87      inference('sup+', [status(thm)], ['42', '63'])).
% 0.71/0.87  thf('65', plain, ((l1_struct_0 @ sk_B)),
% 0.71/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.71/0.87  thf('66', plain,
% 0.71/0.87      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_B)))
% 0.71/0.87         = (u1_struct_0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['64', '65'])).
% 0.71/0.87  thf('67', plain, (((k2_struct_0 @ sk_B) = (u1_struct_0 @ sk_B))),
% 0.71/0.87      inference('sup+', [status(thm)], ['41', '66'])).
% 0.71/0.87  thf('68', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('69', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.71/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.71/0.87  thf('71', plain,
% 0.71/0.87      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['19', '20', '67', '68', '69', '70'])).
% 0.71/0.87  thf('72', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('73', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('74', plain,
% 0.71/0.87      (![X29 : $i, X30 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X29 @ X30)
% 0.71/0.87          | (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.71/0.87             (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.71/0.87          | ~ (l1_pre_topc @ X30))),
% 0.71/0.87      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.71/0.87  thf('75', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | (m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.71/0.87           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.71/0.87      inference('sup-', [status(thm)], ['73', '74'])).
% 0.71/0.87  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('77', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['75', '76'])).
% 0.71/0.87  thf('78', plain,
% 0.71/0.87      (((m1_subset_1 @ (k2_struct_0 @ sk_C_2) @ 
% 0.71/0.87         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['72', '77'])).
% 0.71/0.87  thf('79', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('80', plain,
% 0.71/0.87      (![X23 : $i, X24 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X23 @ X24)
% 0.71/0.87          | (l1_pre_topc @ X23)
% 0.71/0.87          | ~ (l1_pre_topc @ X24))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.71/0.87  thf('81', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.71/0.87      inference('sup-', [status(thm)], ['79', '80'])).
% 0.71/0.87  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('83', plain, ((l1_pre_topc @ sk_C_2)),
% 0.71/0.87      inference('demod', [status(thm)], ['81', '82'])).
% 0.71/0.87  thf('84', plain,
% 0.71/0.87      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.71/0.87  thf('85', plain, ((l1_struct_0 @ sk_C_2)),
% 0.71/0.87      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.87  thf('86', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['78', '85'])).
% 0.71/0.87  thf(d7_subset_1, axiom,
% 0.71/0.87    (![A:$i,B:$i]:
% 0.71/0.87     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.87       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.71/0.87  thf('87', plain,
% 0.71/0.87      (![X34 : $i, X35 : $i]:
% 0.71/0.87         (((X35) = (X34))
% 0.71/0.87          | (v1_subset_1 @ X35 @ X34)
% 0.71/0.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.71/0.87      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.71/0.87  thf('88', plain,
% 0.71/0.87      (((v1_subset_1 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 0.71/0.87        | ((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['86', '87'])).
% 0.71/0.87  thf('89', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('90', plain,
% 0.71/0.87      (![X31 : $i, X32 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X31 @ X32)
% 0.71/0.87          | ((sk_C_1 @ X31 @ X32) = (u1_struct_0 @ X31))
% 0.71/0.87          | (v1_tex_2 @ X31 @ X32)
% 0.71/0.87          | ~ (l1_pre_topc @ X32))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.71/0.87  thf('91', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | (v1_tex_2 @ sk_C_2 @ sk_A)
% 0.71/0.87        | ((sk_C_1 @ sk_C_2 @ sk_A) = (u1_struct_0 @ sk_C_2)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['89', '90'])).
% 0.71/0.87  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('93', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['78', '85'])).
% 0.71/0.87  thf('94', plain,
% 0.71/0.87      (![X6 : $i, X7 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X7)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.71/0.87          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.71/0.87          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.71/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.71/0.87  thf('95', plain,
% 0.71/0.87      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87          = (k2_struct_0 @ sk_C_2))
% 0.71/0.87        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)) @ sk_A)
% 0.71/0.87        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['93', '94'])).
% 0.71/0.87  thf('96', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('97', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['75', '76'])).
% 0.71/0.87  thf('98', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (v1_pre_topc @ (k1_pre_topc @ X20 @ X21)))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('99', plain,
% 0.71/0.87      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['97', '98'])).
% 0.71/0.87  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('101', plain,
% 0.71/0.87      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['99', '100'])).
% 0.71/0.87  thf('102', plain,
% 0.71/0.87      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['96', '101'])).
% 0.71/0.87  thf('103', plain, ((l1_struct_0 @ sk_C_2)),
% 0.71/0.87      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.87  thf('104', plain,
% 0.71/0.87      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['102', '103'])).
% 0.71/0.87  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('106', plain,
% 0.71/0.87      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87          = (k2_struct_0 @ sk_C_2))
% 0.71/0.87        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)) @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['95', '104', '105'])).
% 0.71/0.87  thf('107', plain,
% 0.71/0.87      ((m1_subset_1 @ (k2_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['78', '85'])).
% 0.71/0.87  thf('108', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('109', plain,
% 0.71/0.87      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)) @ sk_A)
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['107', '108'])).
% 0.71/0.87  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('111', plain,
% 0.71/0.87      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)) @ sk_A)),
% 0.71/0.87      inference('demod', [status(thm)], ['109', '110'])).
% 0.71/0.87  thf('112', plain,
% 0.71/0.87      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87         = (k2_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('demod', [status(thm)], ['106', '111'])).
% 0.71/0.87  thf('113', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('114', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('115', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['75', '76'])).
% 0.71/0.87  thf('116', plain,
% 0.71/0.87      (((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.71/0.87         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.87      inference('sup+', [status(thm)], ['114', '115'])).
% 0.71/0.87  thf('117', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.87  thf('118', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['116', '117'])).
% 0.71/0.87  thf('119', plain,
% 0.71/0.87      (![X0 : $i, X1 : $i]:
% 0.71/0.87         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_struct_0 @ X0)
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1))
% 0.71/0.87          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ X1) @ X0)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ X1))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['50', '51'])).
% 0.71/0.87  thf('120', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)))
% 0.71/0.87        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)) @ sk_A)
% 0.71/0.87        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)))
% 0.71/0.87            = (u1_struct_0 @ sk_C_2))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['118', '119'])).
% 0.71/0.87  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('122', plain,
% 0.71/0.87      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['99', '100'])).
% 0.71/0.87  thf('123', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.87  thf('124', plain,
% 0.71/0.87      ((~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)) @ sk_A)
% 0.71/0.87        | ((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)))
% 0.71/0.87            = (u1_struct_0 @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.71/0.87  thf('125', plain,
% 0.71/0.87      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.71/0.87        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.87      inference('demod', [status(thm)], ['75', '76'])).
% 0.71/0.87  thf('126', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('127', plain,
% 0.71/0.87      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)) @ sk_A)
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['125', '126'])).
% 0.71/0.87  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('129', plain,
% 0.71/0.87      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)) @ sk_A)),
% 0.71/0.87      inference('demod', [status(thm)], ['127', '128'])).
% 0.71/0.87  thf('130', plain,
% 0.71/0.87      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_2)))
% 0.71/0.87         = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('demod', [status(thm)], ['124', '129'])).
% 0.71/0.87  thf('131', plain,
% 0.71/0.87      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87          = (u1_struct_0 @ sk_C_2))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['113', '130'])).
% 0.71/0.87  thf('132', plain, ((l1_struct_0 @ sk_C_2)),
% 0.71/0.87      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.87  thf('133', plain,
% 0.71/0.87      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87         = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('demod', [status(thm)], ['131', '132'])).
% 0.71/0.87  thf('134', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['112', '133'])).
% 0.71/0.87  thf('135', plain,
% 0.71/0.87      (((v1_tex_2 @ sk_C_2 @ sk_A)
% 0.71/0.87        | ((sk_C_1 @ sk_C_2 @ sk_A) = (k2_struct_0 @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['91', '92', '134'])).
% 0.71/0.87  thf('136', plain, (~ (v1_tex_2 @ sk_C_2 @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('137', plain, (((sk_C_1 @ sk_C_2 @ sk_A) = (k2_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('clc', [status(thm)], ['135', '136'])).
% 0.71/0.87  thf('138', plain,
% 0.71/0.87      (![X31 : $i, X32 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X31 @ X32)
% 0.71/0.87          | ~ (v1_subset_1 @ (sk_C_1 @ X31 @ X32) @ (u1_struct_0 @ X32))
% 0.71/0.87          | (v1_tex_2 @ X31 @ X32)
% 0.71/0.87          | ~ (l1_pre_topc @ X32))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.71/0.87  thf('139', plain,
% 0.71/0.87      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | (v1_tex_2 @ sk_C_2 @ sk_A)
% 0.71/0.87        | ~ (m1_pre_topc @ sk_C_2 @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['137', '138'])).
% 0.71/0.87  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('141', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('142', plain,
% 0.71/0.87      ((~ (v1_subset_1 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 0.71/0.87        | (v1_tex_2 @ sk_C_2 @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['139', '140', '141'])).
% 0.71/0.87  thf('143', plain, (~ (v1_tex_2 @ sk_C_2 @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('144', plain,
% 0.71/0.87      (~ (v1_subset_1 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.71/0.87      inference('clc', [status(thm)], ['142', '143'])).
% 0.71/0.87  thf('145', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['88', '144'])).
% 0.71/0.87  thf('146', plain,
% 0.71/0.87      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('demod', [status(thm)], ['71', '145'])).
% 0.71/0.87  thf('147', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf(d9_pre_topc, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( l1_pre_topc @ B ) =>
% 0.71/0.87           ( ( m1_pre_topc @ B @ A ) <=>
% 0.71/0.87             ( ( ![C:$i]:
% 0.71/0.87                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.71/0.87                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.71/0.87                     ( ?[D:$i]:
% 0.71/0.87                       ( ( m1_subset_1 @
% 0.71/0.87                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.71/0.87                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.71/0.87                         ( ( C ) =
% 0.71/0.87                           ( k9_subset_1 @
% 0.71/0.87                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.71/0.87               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.71/0.87  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.71/0.87  thf(zf_stmt_2, axiom,
% 0.71/0.87    (![D:$i,C:$i,B:$i,A:$i]:
% 0.71/0.87     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.71/0.87       ( ( ( C ) =
% 0.71/0.87           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.71/0.87         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.71/0.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.71/0.87  thf(zf_stmt_3, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( l1_pre_topc @ B ) =>
% 0.71/0.87           ( ( m1_pre_topc @ B @ A ) <=>
% 0.71/0.87             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.71/0.87               ( ![C:$i]:
% 0.71/0.87                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.71/0.87                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.71/0.87                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.71/0.87  thf('148', plain,
% 0.71/0.87      (![X15 : $i, X16 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X15)
% 0.71/0.87          | ~ (m1_pre_topc @ X15 @ X16)
% 0.71/0.87          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.71/0.87          | ~ (l1_pre_topc @ X16))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.87  thf('149', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.87        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_B))),
% 0.71/0.87      inference('sup-', [status(thm)], ['147', '148'])).
% 0.71/0.87  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('151', plain, ((l1_pre_topc @ sk_B)),
% 0.71/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.87  thf('152', plain,
% 0.71/0.87      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.71/0.87  thf(d10_xboole_0, axiom,
% 0.71/0.87    (![A:$i,B:$i]:
% 0.71/0.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.71/0.87  thf('153', plain,
% 0.71/0.87      (![X0 : $i, X2 : $i]:
% 0.71/0.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.71/0.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.71/0.87  thf('154', plain,
% 0.71/0.87      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.71/0.87        | ((k2_struct_0 @ sk_A) = (k2_struct_0 @ sk_B)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['152', '153'])).
% 0.71/0.87  thf('155', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('156', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_A))),
% 0.71/0.87      inference('sup-', [status(thm)], ['88', '144'])).
% 0.71/0.87  thf('157', plain,
% 0.71/0.87      ((((k2_struct_0 @ sk_C_2) = (k2_struct_0 @ sk_A))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.87      inference('sup+', [status(thm)], ['155', '156'])).
% 0.71/0.87  thf('158', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.71/0.87  thf('159', plain, (((k2_struct_0 @ sk_C_2) = (k2_struct_0 @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['157', '158'])).
% 0.71/0.87  thf('160', plain, (((k2_struct_0 @ sk_C_2) = (k2_struct_0 @ sk_A))),
% 0.71/0.87      inference('demod', [status(thm)], ['157', '158'])).
% 0.71/0.87  thf('161', plain,
% 0.71/0.87      ((~ (r1_tarski @ (k2_struct_0 @ sk_C_2) @ (k2_struct_0 @ sk_B))
% 0.71/0.87        | ((k2_struct_0 @ sk_C_2) = (k2_struct_0 @ sk_B)))),
% 0.71/0.87      inference('demod', [status(thm)], ['154', '159', '160'])).
% 0.71/0.87  thf('162', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['112', '133'])).
% 0.71/0.87  thf(dt_k2_subset_1, axiom,
% 0.71/0.87    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.71/0.87  thf('163', plain,
% 0.71/0.87      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.71/0.87  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.71/0.87  thf('164', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.71/0.87      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.71/0.87  thf('165', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.71/0.87      inference('demod', [status(thm)], ['163', '164'])).
% 0.71/0.87  thf('166', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('167', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['165', '166'])).
% 0.71/0.87  thf(t65_pre_topc, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( l1_pre_topc @ B ) =>
% 0.71/0.87           ( ( m1_pre_topc @ A @ B ) <=>
% 0.71/0.87             ( m1_pre_topc @
% 0.71/0.87               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.71/0.87  thf('168', plain,
% 0.71/0.87      (![X27 : $i, X28 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X27)
% 0.71/0.87          | ~ (m1_pre_topc @ X28 @ X27)
% 0.71/0.87          | (m1_pre_topc @ X28 @ 
% 0.71/0.87             (g1_pre_topc @ (u1_struct_0 @ X27) @ (u1_pre_topc @ X27)))
% 0.71/0.87          | ~ (l1_pre_topc @ X28))),
% 0.71/0.87      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.71/0.87  thf('169', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X0)
% 0.71/0.87          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.71/0.87             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['167', '168'])).
% 0.71/0.87  thf('170', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.71/0.87           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('simplify', [status(thm)], ['169'])).
% 0.71/0.87  thf('171', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['165', '166'])).
% 0.71/0.87  thf('172', plain,
% 0.71/0.87      (![X23 : $i, X24 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X23 @ X24)
% 0.71/0.87          | (l1_pre_topc @ X23)
% 0.71/0.87          | ~ (l1_pre_topc @ X24))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.71/0.87  thf('173', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X0)
% 0.71/0.87          | ~ (l1_pre_topc @ X0)
% 0.71/0.87          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.71/0.87      inference('sup-', [status(thm)], ['171', '172'])).
% 0.71/0.87  thf('174', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('simplify', [status(thm)], ['173'])).
% 0.71/0.87  thf('175', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X0)
% 0.71/0.87          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.71/0.87             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.71/0.87      inference('clc', [status(thm)], ['170', '174'])).
% 0.71/0.87  thf('176', plain,
% 0.71/0.87      (((m1_pre_topc @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2)) @ 
% 0.71/0.87         (g1_pre_topc @ (u1_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['162', '175'])).
% 0.71/0.87  thf('177', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['112', '133'])).
% 0.71/0.87  thf('178', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('179', plain,
% 0.71/0.87      (![X9 : $i]:
% 0.71/0.87         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.71/0.87      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.87  thf('180', plain,
% 0.71/0.87      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.71/0.87         = (g1_pre_topc @ (u1_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.87  thf('181', plain,
% 0.71/0.87      ((((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.71/0.87          = (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['179', '180'])).
% 0.71/0.87  thf('182', plain, ((l1_struct_0 @ sk_C_2)),
% 0.71/0.87      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.87  thf('183', plain,
% 0.71/0.87      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.71/0.87         = (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['181', '182'])).
% 0.71/0.87  thf('184', plain,
% 0.71/0.87      ((((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.71/0.87          = (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))
% 0.71/0.87        | ~ (l1_struct_0 @ sk_B))),
% 0.71/0.87      inference('sup+', [status(thm)], ['178', '183'])).
% 0.71/0.87  thf('185', plain, ((l1_struct_0 @ sk_B)),
% 0.71/0.87      inference('sup-', [status(thm)], ['11', '12'])).
% 0.71/0.87  thf('186', plain,
% 0.71/0.87      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.71/0.87         = (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['184', '185'])).
% 0.71/0.87  thf('187', plain, ((l1_pre_topc @ sk_C_2)),
% 0.71/0.87      inference('demod', [status(thm)], ['81', '82'])).
% 0.71/0.87  thf('188', plain,
% 0.71/0.87      ((m1_pre_topc @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2)) @ 
% 0.71/0.87        (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.71/0.87      inference('demod', [status(thm)], ['176', '177', '186', '187'])).
% 0.71/0.87  thf('189', plain,
% 0.71/0.87      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.71/0.87         = (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['181', '182'])).
% 0.71/0.87  thf(t59_pre_topc, axiom,
% 0.71/0.87    (![A:$i]:
% 0.71/0.87     ( ( l1_pre_topc @ A ) =>
% 0.71/0.87       ( ![B:$i]:
% 0.71/0.87         ( ( m1_pre_topc @
% 0.71/0.87             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.71/0.87           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.71/0.87  thf('190', plain,
% 0.71/0.87      (![X25 : $i, X26 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X25 @ 
% 0.71/0.87             (g1_pre_topc @ (u1_struct_0 @ X26) @ (u1_pre_topc @ X26)))
% 0.71/0.87          | (m1_pre_topc @ X25 @ X26)
% 0.71/0.87          | ~ (l1_pre_topc @ X26))),
% 0.71/0.87      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.71/0.87  thf('191', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X0 @ 
% 0.71/0.87             (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))
% 0.71/0.87          | ~ (l1_pre_topc @ sk_B)
% 0.71/0.87          | (m1_pre_topc @ X0 @ sk_B))),
% 0.71/0.87      inference('sup-', [status(thm)], ['189', '190'])).
% 0.71/0.87  thf('192', plain, ((l1_pre_topc @ sk_B)),
% 0.71/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.87  thf('193', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X0 @ 
% 0.71/0.87             (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))
% 0.71/0.87          | (m1_pre_topc @ X0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['191', '192'])).
% 0.71/0.87  thf('194', plain,
% 0.71/0.87      (((g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.71/0.87         = (g1_pre_topc @ (k2_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['184', '185'])).
% 0.71/0.87  thf('195', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (m1_pre_topc @ X0 @ 
% 0.71/0.87             (g1_pre_topc @ (k2_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.71/0.87          | (m1_pre_topc @ X0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['193', '194'])).
% 0.71/0.87  thf('196', plain,
% 0.71/0.87      ((m1_pre_topc @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2)) @ sk_B)),
% 0.71/0.87      inference('sup-', [status(thm)], ['188', '195'])).
% 0.71/0.87  thf('197', plain,
% 0.71/0.87      (![X15 : $i, X16 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X15)
% 0.71/0.87          | ~ (m1_pre_topc @ X15 @ X16)
% 0.71/0.87          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.71/0.87          | ~ (l1_pre_topc @ X16))),
% 0.71/0.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.87  thf('198', plain,
% 0.71/0.87      ((~ (l1_pre_topc @ sk_B)
% 0.71/0.87        | (r1_tarski @ 
% 0.71/0.87           (k2_struct_0 @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2))) @ 
% 0.71/0.87           (k2_struct_0 @ sk_B))
% 0.71/0.87        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2))))),
% 0.71/0.87      inference('sup-', [status(thm)], ['196', '197'])).
% 0.71/0.87  thf('199', plain, ((l1_pre_topc @ sk_B)),
% 0.71/0.87      inference('demod', [status(thm)], ['9', '10'])).
% 0.71/0.87  thf('200', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['112', '133'])).
% 0.71/0.87  thf('201', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['165', '166'])).
% 0.71/0.87  thf('202', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.71/0.87      inference('demod', [status(thm)], ['163', '164'])).
% 0.71/0.87  thf('203', plain,
% 0.71/0.87      (![X6 : $i, X7 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X7)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X7 @ X6))
% 0.71/0.87          | ~ (m1_pre_topc @ (k1_pre_topc @ X7 @ X6) @ X7)
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X7 @ X6)) = (X6))
% 0.71/0.87          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.71/0.87      inference('simplify', [status(thm)], ['22'])).
% 0.71/0.87  thf('204', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87            = (u1_struct_0 @ X0))
% 0.71/0.87          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ X0)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['202', '203'])).
% 0.71/0.87  thf('205', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X0)
% 0.71/0.87          | ~ (l1_pre_topc @ X0)
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87              = (u1_struct_0 @ X0)))),
% 0.71/0.87      inference('sup-', [status(thm)], ['201', '204'])).
% 0.71/0.87  thf('206', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87            = (u1_struct_0 @ X0))
% 0.71/0.87          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('simplify', [status(thm)], ['205'])).
% 0.71/0.87  thf('207', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.71/0.87      inference('demod', [status(thm)], ['163', '164'])).
% 0.71/0.87  thf('208', plain,
% 0.71/0.87      (![X20 : $i, X21 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X20)
% 0.71/0.87          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.71/0.87          | (v1_pre_topc @ (k1_pre_topc @ X20 @ X21)))),
% 0.71/0.87      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.71/0.87  thf('209', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((v1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('sup-', [status(thm)], ['207', '208'])).
% 0.71/0.87  thf('210', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         (~ (l1_pre_topc @ X0)
% 0.71/0.87          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87              = (u1_struct_0 @ X0)))),
% 0.71/0.87      inference('clc', [status(thm)], ['206', '209'])).
% 0.71/0.87  thf('211', plain,
% 0.71/0.87      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87          = (u1_struct_0 @ sk_C_2))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['200', '210'])).
% 0.71/0.87  thf('212', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['112', '133'])).
% 0.71/0.87  thf('213', plain, ((l1_pre_topc @ sk_C_2)),
% 0.71/0.87      inference('demod', [status(thm)], ['81', '82'])).
% 0.71/0.87  thf('214', plain,
% 0.71/0.87      (((k2_struct_0 @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87         = (k2_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('demod', [status(thm)], ['211', '212', '213'])).
% 0.71/0.87  thf('215', plain, (((k2_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['112', '133'])).
% 0.71/0.87  thf('216', plain,
% 0.71/0.87      (![X0 : $i]:
% 0.71/0.87         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.71/0.87          | ~ (l1_pre_topc @ X0))),
% 0.71/0.87      inference('simplify', [status(thm)], ['173'])).
% 0.71/0.87  thf('217', plain,
% 0.71/0.87      (((l1_pre_topc @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2)))
% 0.71/0.87        | ~ (l1_pre_topc @ sk_C_2))),
% 0.71/0.87      inference('sup+', [status(thm)], ['215', '216'])).
% 0.71/0.87  thf('218', plain, ((l1_pre_topc @ sk_C_2)),
% 0.71/0.87      inference('demod', [status(thm)], ['81', '82'])).
% 0.71/0.87  thf('219', plain,
% 0.71/0.87      ((l1_pre_topc @ (k1_pre_topc @ sk_C_2 @ (k2_struct_0 @ sk_C_2)))),
% 0.71/0.87      inference('demod', [status(thm)], ['217', '218'])).
% 0.71/0.87  thf('220', plain,
% 0.71/0.87      ((r1_tarski @ (k2_struct_0 @ sk_C_2) @ (k2_struct_0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['198', '199', '214', '219'])).
% 0.71/0.87  thf('221', plain, (((k2_struct_0 @ sk_C_2) = (k2_struct_0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['161', '220'])).
% 0.71/0.87  thf('222', plain,
% 0.71/0.87      ((v1_subset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))),
% 0.71/0.87      inference('demod', [status(thm)], ['146', '221'])).
% 0.71/0.87  thf(fc14_subset_1, axiom,
% 0.71/0.87    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.71/0.87  thf('223', plain, (![X5 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X5) @ X5)),
% 0.71/0.87      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.71/0.87  thf('224', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.71/0.87      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.71/0.87  thf('225', plain, (![X5 : $i]: ~ (v1_subset_1 @ X5 @ X5)),
% 0.71/0.87      inference('demod', [status(thm)], ['223', '224'])).
% 0.71/0.87  thf('226', plain, ($false), inference('sup-', [status(thm)], ['222', '225'])).
% 0.71/0.87  
% 0.71/0.87  % SZS output end Refutation
% 0.71/0.87  
% 0.71/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

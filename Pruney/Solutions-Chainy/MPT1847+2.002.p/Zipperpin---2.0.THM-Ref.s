%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jtYdnIWqxb

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:53 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 335 expanded)
%              Number of leaves         :   31 ( 107 expanded)
%              Depth                    :   18
%              Number of atoms          :  879 (4126 expanded)
%              Number of equality atoms :   29 ( 140 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( v1_tex_2 @ X32 @ X33 )
      | ( X34
       != ( u1_struct_0 @ X32 ) )
      | ( v1_subset_1 @ X34 @ ( u1_struct_0 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X32 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( v1_tex_2 @ X32 @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('17',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X36 = X35 )
      | ( v1_subset_1 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('18',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( ( sk_C_1 @ X32 @ X33 )
        = ( u1_struct_0 @ X32 ) )
      | ( v1_tex_2 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ( ( sk_C_1 @ sk_C_2 @ sk_A )
      = ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ( ( sk_C_1 @ sk_C_2 @ sk_A )
      = ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_A )
    = ( u1_struct_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X32 @ X33 ) @ ( u1_struct_0 @ X33 ) )
      | ( v1_tex_2 @ X32 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('27',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ~ ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( u1_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['11','33'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('35',plain,(
    ! [X29: $i] :
      ( ( m1_pre_topc @ X29 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X24 @ X23 )
      | ( m1_pre_topc @ X24 @ ( g1_pre_topc @ ( u1_struct_0 @ X23 ) @ ( u1_pre_topc @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ( m1_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C_2 )
      | ( m1_pre_topc @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_pre_topc @ sk_B @ sk_C_2 ),
    inference(demod,[status(thm)],['48','53'])).

thf('55',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['44','45'])).

thf('58',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('59',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ( X11 = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('60',plain,
    ( ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('61',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('62',plain,
    ( ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('64',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( v1_subset_1 @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( u1_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_C_2 ) )
    | ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['62','69'])).

thf('71',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('73',plain,
    ( ( m1_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['44','45'])).

thf('75',plain,(
    m1_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ ( g1_pre_topc @ ( u1_struct_0 @ X22 ) @ ( u1_pre_topc @ X22 ) ) )
      | ( m1_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('79',plain,(
    m1_pre_topc @ sk_C_2 @ sk_B ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('83',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('84',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) )
    | ( r2_hidden @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','85'])).

thf('87',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X10 @ X11 ) @ X10 )
      | ( X11 = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('88',plain,
    ( ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) )
    | ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['34','91'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('93',plain,(
    ! [X16: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('94',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('95',plain,(
    ! [X16: $i] :
      ~ ( v1_subset_1 @ X16 @ X16 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference('sup-',[status(thm)],['92','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jtYdnIWqxb
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.67/0.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.85  % Solved by: fo/fo7.sh
% 0.67/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.85  % done 560 iterations in 0.407s
% 0.67/0.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.85  % SZS output start Refutation
% 0.67/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.85  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.67/0.85  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.67/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.85  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.67/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.85  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.67/0.85  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.67/0.85  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.85  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.67/0.85  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.67/0.85  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.67/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.85  thf(t14_tex_2, conjecture,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_pre_topc @ A ) =>
% 0.67/0.85       ( ![B:$i]:
% 0.67/0.85         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.85           ( ![C:$i]:
% 0.67/0.85             ( ( m1_pre_topc @ C @ A ) =>
% 0.67/0.85               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.67/0.85                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.67/0.85                   ( v1_tex_2 @ B @ A ) ) =>
% 0.67/0.85                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.67/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.85    (~( ![A:$i]:
% 0.67/0.85        ( ( l1_pre_topc @ A ) =>
% 0.67/0.85          ( ![B:$i]:
% 0.67/0.85            ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.85              ( ![C:$i]:
% 0.67/0.85                ( ( m1_pre_topc @ C @ A ) =>
% 0.67/0.85                  ( ( ( ( g1_pre_topc @
% 0.67/0.85                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.67/0.85                        ( g1_pre_topc @
% 0.67/0.85                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.67/0.85                      ( v1_tex_2 @ B @ A ) ) =>
% 0.67/0.85                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.67/0.85    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.67/0.85  thf('0', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf(t1_tsep_1, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_pre_topc @ A ) =>
% 0.67/0.85       ( ![B:$i]:
% 0.67/0.85         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.85           ( m1_subset_1 @
% 0.67/0.85             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.67/0.85  thf('1', plain,
% 0.67/0.85      (![X27 : $i, X28 : $i]:
% 0.67/0.85         (~ (m1_pre_topc @ X27 @ X28)
% 0.67/0.85          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.67/0.85             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.67/0.85          | ~ (l1_pre_topc @ X28))),
% 0.67/0.85      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.85  thf('2', plain,
% 0.67/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.85        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.67/0.85  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('4', plain,
% 0.67/0.85      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.85      inference('demod', [status(thm)], ['2', '3'])).
% 0.67/0.85  thf(d3_tex_2, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_pre_topc @ A ) =>
% 0.67/0.85       ( ![B:$i]:
% 0.67/0.85         ( ( m1_pre_topc @ B @ A ) =>
% 0.67/0.85           ( ( v1_tex_2 @ B @ A ) <=>
% 0.67/0.85             ( ![C:$i]:
% 0.67/0.85               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.85                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.67/0.85                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.67/0.85  thf('5', plain,
% 0.67/0.85      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.67/0.85         (~ (m1_pre_topc @ X32 @ X33)
% 0.67/0.85          | ~ (v1_tex_2 @ X32 @ X33)
% 0.67/0.85          | ((X34) != (u1_struct_0 @ X32))
% 0.67/0.85          | (v1_subset_1 @ X34 @ (u1_struct_0 @ X33))
% 0.67/0.85          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.67/0.85          | ~ (l1_pre_topc @ X33))),
% 0.67/0.85      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.85  thf('6', plain,
% 0.67/0.85      (![X32 : $i, X33 : $i]:
% 0.67/0.85         (~ (l1_pre_topc @ X33)
% 0.67/0.85          | ~ (m1_subset_1 @ (u1_struct_0 @ X32) @ 
% 0.67/0.85               (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.67/0.85          | (v1_subset_1 @ (u1_struct_0 @ X32) @ (u1_struct_0 @ X33))
% 0.67/0.85          | ~ (v1_tex_2 @ X32 @ X33)
% 0.67/0.85          | ~ (m1_pre_topc @ X32 @ X33))),
% 0.67/0.85      inference('simplify', [status(thm)], ['5'])).
% 0.67/0.85  thf('7', plain,
% 0.67/0.85      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.67/0.85        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.67/0.85        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.67/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.67/0.85      inference('sup-', [status(thm)], ['4', '6'])).
% 0.67/0.85  thf('8', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('9', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('11', plain,
% 0.67/0.85      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.85      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.67/0.85  thf('12', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('13', plain,
% 0.67/0.85      (![X27 : $i, X28 : $i]:
% 0.67/0.85         (~ (m1_pre_topc @ X27 @ X28)
% 0.67/0.85          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.67/0.85             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.67/0.85          | ~ (l1_pre_topc @ X28))),
% 0.67/0.85      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.85  thf('14', plain,
% 0.67/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.85        | (m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.67/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.67/0.85      inference('sup-', [status(thm)], ['12', '13'])).
% 0.67/0.85  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('16', plain,
% 0.67/0.85      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.67/0.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.85      inference('demod', [status(thm)], ['14', '15'])).
% 0.67/0.85  thf(d7_subset_1, axiom,
% 0.67/0.85    (![A:$i,B:$i]:
% 0.67/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.85       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.67/0.85  thf('17', plain,
% 0.67/0.85      (![X35 : $i, X36 : $i]:
% 0.67/0.85         (((X36) = (X35))
% 0.67/0.85          | (v1_subset_1 @ X36 @ X35)
% 0.67/0.85          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35)))),
% 0.67/0.85      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.67/0.85  thf('18', plain,
% 0.67/0.85      (((v1_subset_1 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 0.67/0.85        | ((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_A)))),
% 0.67/0.85      inference('sup-', [status(thm)], ['16', '17'])).
% 0.67/0.85  thf('19', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('20', plain,
% 0.67/0.85      (![X32 : $i, X33 : $i]:
% 0.67/0.85         (~ (m1_pre_topc @ X32 @ X33)
% 0.67/0.85          | ((sk_C_1 @ X32 @ X33) = (u1_struct_0 @ X32))
% 0.67/0.85          | (v1_tex_2 @ X32 @ X33)
% 0.67/0.85          | ~ (l1_pre_topc @ X33))),
% 0.67/0.85      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.85  thf('21', plain,
% 0.67/0.85      ((~ (l1_pre_topc @ sk_A)
% 0.67/0.85        | (v1_tex_2 @ sk_C_2 @ sk_A)
% 0.67/0.85        | ((sk_C_1 @ sk_C_2 @ sk_A) = (u1_struct_0 @ sk_C_2)))),
% 0.67/0.85      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.85  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('23', plain,
% 0.67/0.85      (((v1_tex_2 @ sk_C_2 @ sk_A)
% 0.67/0.85        | ((sk_C_1 @ sk_C_2 @ sk_A) = (u1_struct_0 @ sk_C_2)))),
% 0.67/0.85      inference('demod', [status(thm)], ['21', '22'])).
% 0.67/0.85  thf('24', plain, (~ (v1_tex_2 @ sk_C_2 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('25', plain, (((sk_C_1 @ sk_C_2 @ sk_A) = (u1_struct_0 @ sk_C_2))),
% 0.67/0.85      inference('clc', [status(thm)], ['23', '24'])).
% 0.67/0.85  thf('26', plain,
% 0.67/0.85      (![X32 : $i, X33 : $i]:
% 0.67/0.85         (~ (m1_pre_topc @ X32 @ X33)
% 0.67/0.85          | ~ (v1_subset_1 @ (sk_C_1 @ X32 @ X33) @ (u1_struct_0 @ X33))
% 0.67/0.85          | (v1_tex_2 @ X32 @ X33)
% 0.67/0.85          | ~ (l1_pre_topc @ X33))),
% 0.67/0.85      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.67/0.85  thf('27', plain,
% 0.67/0.85      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 0.67/0.85        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.85        | (v1_tex_2 @ sk_C_2 @ sk_A)
% 0.67/0.85        | ~ (m1_pre_topc @ sk_C_2 @ sk_A))),
% 0.67/0.85      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.85  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('29', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('30', plain,
% 0.67/0.85      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))
% 0.67/0.85        | (v1_tex_2 @ sk_C_2 @ sk_A))),
% 0.67/0.85      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.67/0.85  thf('31', plain, (~ (v1_tex_2 @ sk_C_2 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf('32', plain,
% 0.67/0.85      (~ (v1_subset_1 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.67/0.85      inference('clc', [status(thm)], ['30', '31'])).
% 0.67/0.85  thf('33', plain, (((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_A))),
% 0.67/0.85      inference('sup-', [status(thm)], ['18', '32'])).
% 0.67/0.85  thf('34', plain,
% 0.67/0.85      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2))),
% 0.67/0.85      inference('demod', [status(thm)], ['11', '33'])).
% 0.67/0.85  thf(t2_tsep_1, axiom,
% 0.67/0.85    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.67/0.85  thf('35', plain,
% 0.67/0.85      (![X29 : $i]: ((m1_pre_topc @ X29 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.67/0.85      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.67/0.85  thf(t65_pre_topc, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_pre_topc @ A ) =>
% 0.67/0.85       ( ![B:$i]:
% 0.67/0.85         ( ( l1_pre_topc @ B ) =>
% 0.67/0.85           ( ( m1_pre_topc @ A @ B ) <=>
% 0.67/0.85             ( m1_pre_topc @
% 0.67/0.85               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.67/0.85  thf('36', plain,
% 0.67/0.85      (![X23 : $i, X24 : $i]:
% 0.67/0.85         (~ (l1_pre_topc @ X23)
% 0.67/0.85          | ~ (m1_pre_topc @ X24 @ X23)
% 0.67/0.85          | (m1_pre_topc @ X24 @ 
% 0.67/0.85             (g1_pre_topc @ (u1_struct_0 @ X23) @ (u1_pre_topc @ X23)))
% 0.67/0.85          | ~ (l1_pre_topc @ X24))),
% 0.67/0.85      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.67/0.85  thf('37', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         (~ (l1_pre_topc @ X0)
% 0.67/0.85          | ~ (l1_pre_topc @ X0)
% 0.67/0.85          | (m1_pre_topc @ X0 @ 
% 0.67/0.85             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.67/0.85          | ~ (l1_pre_topc @ X0))),
% 0.67/0.85      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.85  thf('38', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         ((m1_pre_topc @ X0 @ 
% 0.67/0.85           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.67/0.85          | ~ (l1_pre_topc @ X0))),
% 0.67/0.85      inference('simplify', [status(thm)], ['37'])).
% 0.67/0.85  thf('39', plain,
% 0.67/0.85      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.85         = (g1_pre_topc @ (u1_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf(t59_pre_topc, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_pre_topc @ A ) =>
% 0.67/0.85       ( ![B:$i]:
% 0.67/0.85         ( ( m1_pre_topc @
% 0.67/0.85             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.67/0.85           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.67/0.85  thf('40', plain,
% 0.67/0.85      (![X21 : $i, X22 : $i]:
% 0.67/0.85         (~ (m1_pre_topc @ X21 @ 
% 0.67/0.85             (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.67/0.85          | (m1_pre_topc @ X21 @ X22)
% 0.67/0.85          | ~ (l1_pre_topc @ X22))),
% 0.67/0.85      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.67/0.85  thf('41', plain,
% 0.67/0.85      (![X0 : $i]:
% 0.67/0.85         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.85             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.67/0.85          | ~ (l1_pre_topc @ sk_C_2)
% 0.67/0.85          | (m1_pre_topc @ X0 @ sk_C_2))),
% 0.67/0.85      inference('sup-', [status(thm)], ['39', '40'])).
% 0.67/0.85  thf('42', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.67/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.85  thf(dt_m1_pre_topc, axiom,
% 0.67/0.85    (![A:$i]:
% 0.67/0.85     ( ( l1_pre_topc @ A ) =>
% 0.67/0.85       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.67/0.86  thf('43', plain,
% 0.67/0.86      (![X19 : $i, X20 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X19 @ X20)
% 0.67/0.86          | (l1_pre_topc @ X19)
% 0.67/0.86          | ~ (l1_pre_topc @ X20))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.86  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.67/0.86      inference('sup-', [status(thm)], ['42', '43'])).
% 0.67/0.86  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('46', plain, ((l1_pre_topc @ sk_C_2)),
% 0.67/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.67/0.86  thf('47', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X0 @ 
% 0.67/0.86             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.67/0.86          | (m1_pre_topc @ X0 @ sk_C_2))),
% 0.67/0.86      inference('demod', [status(thm)], ['41', '46'])).
% 0.67/0.86  thf('48', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_B @ sk_C_2))),
% 0.67/0.86      inference('sup-', [status(thm)], ['38', '47'])).
% 0.67/0.86  thf('49', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('50', plain,
% 0.67/0.86      (![X19 : $i, X20 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X19 @ X20)
% 0.67/0.86          | (l1_pre_topc @ X19)
% 0.67/0.86          | ~ (l1_pre_topc @ X20))),
% 0.67/0.86      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.67/0.86  thf('51', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['49', '50'])).
% 0.67/0.86  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('53', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['51', '52'])).
% 0.67/0.86  thf('54', plain, ((m1_pre_topc @ sk_B @ sk_C_2)),
% 0.67/0.86      inference('demod', [status(thm)], ['48', '53'])).
% 0.67/0.86  thf('55', plain,
% 0.67/0.86      (![X27 : $i, X28 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X27 @ X28)
% 0.67/0.86          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.67/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.67/0.86          | ~ (l1_pre_topc @ X28))),
% 0.67/0.86      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.86  thf('56', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_C_2)
% 0.67/0.86        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['54', '55'])).
% 0.67/0.86  thf('57', plain, ((l1_pre_topc @ sk_C_2)),
% 0.67/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.67/0.86  thf('58', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))),
% 0.67/0.86      inference('demod', [status(thm)], ['56', '57'])).
% 0.67/0.86  thf(t49_subset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.86       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.67/0.86         ( ( A ) = ( B ) ) ) ))).
% 0.67/0.86  thf('59', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         ((m1_subset_1 @ (sk_C @ X10 @ X11) @ X11)
% 0.67/0.86          | ((X11) = (X10))
% 0.67/0.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.67/0.86  thf('60', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B))
% 0.67/0.86        | (m1_subset_1 @ 
% 0.67/0.86           (sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2)) @ 
% 0.67/0.86           (u1_struct_0 @ sk_C_2)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['58', '59'])).
% 0.67/0.86  thf(d2_subset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( v1_xboole_0 @ A ) =>
% 0.67/0.86         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.67/0.86       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.67/0.86         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.86  thf('61', plain,
% 0.67/0.86      (![X3 : $i, X4 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X3 @ X4)
% 0.67/0.86          | (r2_hidden @ X3 @ X4)
% 0.67/0.86          | (v1_xboole_0 @ X4))),
% 0.67/0.86      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.67/0.86  thf('62', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B))
% 0.67/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_C_2))
% 0.67/0.86        | (r2_hidden @ 
% 0.67/0.86           (sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2)) @ 
% 0.67/0.86           (u1_struct_0 @ sk_C_2)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['60', '61'])).
% 0.67/0.86  thf('63', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('demod', [status(thm)], ['2', '3'])).
% 0.67/0.86  thf(cc4_subset_1, axiom,
% 0.67/0.86    (![A:$i]:
% 0.67/0.86     ( ( v1_xboole_0 @ A ) =>
% 0.67/0.86       ( ![B:$i]:
% 0.67/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.86           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.67/0.86  thf('64', plain,
% 0.67/0.86      (![X14 : $i, X15 : $i]:
% 0.67/0.86         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.67/0.86          | ~ (v1_subset_1 @ X14 @ X15)
% 0.67/0.86          | ~ (v1_xboole_0 @ X15))),
% 0.67/0.86      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.67/0.86  thf('65', plain,
% 0.67/0.86      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.67/0.86        | ~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['63', '64'])).
% 0.67/0.86  thf('66', plain,
% 0.67/0.86      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.67/0.86  thf('67', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('demod', [status(thm)], ['65', '66'])).
% 0.67/0.86  thf('68', plain, (((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_A))),
% 0.67/0.86      inference('sup-', [status(thm)], ['18', '32'])).
% 0.67/0.86  thf('69', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_C_2))),
% 0.67/0.86      inference('demod', [status(thm)], ['67', '68'])).
% 0.67/0.86  thf('70', plain,
% 0.67/0.86      (((r2_hidden @ (sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2)) @ 
% 0.67/0.86         (u1_struct_0 @ sk_C_2))
% 0.67/0.86        | ((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('clc', [status(thm)], ['62', '69'])).
% 0.67/0.86  thf('71', plain,
% 0.67/0.86      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.67/0.86         = (g1_pre_topc @ (u1_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('72', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((m1_pre_topc @ X0 @ 
% 0.67/0.86           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.67/0.86          | ~ (l1_pre_topc @ X0))),
% 0.67/0.86      inference('simplify', [status(thm)], ['37'])).
% 0.67/0.86  thf('73', plain,
% 0.67/0.86      (((m1_pre_topc @ sk_C_2 @ 
% 0.67/0.86         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.67/0.86        | ~ (l1_pre_topc @ sk_C_2))),
% 0.67/0.86      inference('sup+', [status(thm)], ['71', '72'])).
% 0.67/0.86  thf('74', plain, ((l1_pre_topc @ sk_C_2)),
% 0.67/0.86      inference('demod', [status(thm)], ['44', '45'])).
% 0.67/0.86  thf('75', plain,
% 0.67/0.86      ((m1_pre_topc @ sk_C_2 @ 
% 0.67/0.86        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['73', '74'])).
% 0.67/0.86  thf('76', plain,
% 0.67/0.86      (![X21 : $i, X22 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X21 @ 
% 0.67/0.86             (g1_pre_topc @ (u1_struct_0 @ X22) @ (u1_pre_topc @ X22)))
% 0.67/0.86          | (m1_pre_topc @ X21 @ X22)
% 0.67/0.86          | ~ (l1_pre_topc @ X22))),
% 0.67/0.86      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.67/0.86  thf('77', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_C_2 @ sk_B))),
% 0.67/0.86      inference('sup-', [status(thm)], ['75', '76'])).
% 0.67/0.86  thf('78', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['51', '52'])).
% 0.67/0.86  thf('79', plain, ((m1_pre_topc @ sk_C_2 @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['77', '78'])).
% 0.67/0.86  thf('80', plain,
% 0.67/0.86      (![X27 : $i, X28 : $i]:
% 0.67/0.86         (~ (m1_pre_topc @ X27 @ X28)
% 0.67/0.86          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.67/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.67/0.86          | ~ (l1_pre_topc @ X28))),
% 0.67/0.86      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.67/0.86  thf('81', plain,
% 0.67/0.86      ((~ (l1_pre_topc @ sk_B)
% 0.67/0.86        | (m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.67/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.67/0.86      inference('sup-', [status(thm)], ['79', '80'])).
% 0.67/0.86  thf('82', plain, ((l1_pre_topc @ sk_B)),
% 0.67/0.86      inference('demod', [status(thm)], ['51', '52'])).
% 0.67/0.86  thf('83', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['81', '82'])).
% 0.67/0.86  thf(l3_subset_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.86       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.67/0.86  thf('84', plain,
% 0.67/0.86      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.67/0.86         (~ (r2_hidden @ X7 @ X8)
% 0.67/0.86          | (r2_hidden @ X7 @ X9)
% 0.67/0.86          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.67/0.86      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.67/0.86  thf('85', plain,
% 0.67/0.86      (![X0 : $i]:
% 0.67/0.86         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_B))
% 0.67/0.86          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_C_2)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['83', '84'])).
% 0.67/0.86  thf('86', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B))
% 0.67/0.86        | (r2_hidden @ 
% 0.67/0.86           (sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2)) @ 
% 0.67/0.86           (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['70', '85'])).
% 0.67/0.86  thf('87', plain,
% 0.67/0.86      (![X10 : $i, X11 : $i]:
% 0.67/0.86         (~ (r2_hidden @ (sk_C @ X10 @ X11) @ X10)
% 0.67/0.86          | ((X11) = (X10))
% 0.67/0.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.67/0.86      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.67/0.86  thf('88', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B))
% 0.67/0.86        | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))
% 0.67/0.86        | ((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('sup-', [status(thm)], ['86', '87'])).
% 0.67/0.86  thf('89', plain,
% 0.67/0.86      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.67/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))),
% 0.67/0.86      inference('demod', [status(thm)], ['56', '57'])).
% 0.67/0.86  thf('90', plain,
% 0.67/0.86      ((((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B))
% 0.67/0.86        | ((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B)))),
% 0.67/0.86      inference('demod', [status(thm)], ['88', '89'])).
% 0.67/0.86  thf('91', plain, (((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('simplify', [status(thm)], ['90'])).
% 0.67/0.86  thf('92', plain,
% 0.67/0.86      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))),
% 0.67/0.86      inference('demod', [status(thm)], ['34', '91'])).
% 0.67/0.86  thf(fc14_subset_1, axiom,
% 0.67/0.86    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.67/0.86  thf('93', plain, (![X16 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X16) @ X16)),
% 0.67/0.86      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.67/0.86  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.67/0.86  thf('94', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.67/0.86      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.67/0.86  thf('95', plain, (![X16 : $i]: ~ (v1_subset_1 @ X16 @ X16)),
% 0.67/0.86      inference('demod', [status(thm)], ['93', '94'])).
% 0.67/0.86  thf('96', plain, ($false), inference('sup-', [status(thm)], ['92', '95'])).
% 0.67/0.86  
% 0.67/0.86  % SZS output end Refutation
% 0.67/0.86  
% 0.67/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

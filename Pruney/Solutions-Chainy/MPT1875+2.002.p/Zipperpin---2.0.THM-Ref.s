%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yB9TdWcnmP

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:51 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 488 expanded)
%              Number of leaves         :   42 ( 157 expanded)
%              Depth                    :   20
%              Number of atoms          :  929 (5080 expanded)
%              Number of equality atoms :   29 (  69 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_borsuk_1_type,type,(
    v1_borsuk_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X37 @ X38 ) @ X37 )
      | ( v2_tex_2 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ),
    inference(clc,[status(thm)],['8','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( sk_C_1 @ sk_B_1 @ sk_A )
      = sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X26 @ X25 ) )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X24: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ~ ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('26',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('33',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['23','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( X36
       != ( u1_struct_0 @ X34 ) )
      | ~ ( v1_tdlat_3 @ X34 )
      | ( v2_tex_2 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('39',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X34 ) @ X35 )
      | ~ ( v1_tdlat_3 @ X34 )
      | ~ ( m1_pre_topc @ X34 @ X35 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf(cc5_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_borsuk_1 @ B @ A )
            & ( v1_tsep_1 @ B @ A )
            & ( v1_tdlat_3 @ B ) ) ) ) )).

thf('42',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( v1_tdlat_3 @ X32 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v1_tdlat_3 @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[cc5_tdlat_3])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_tdlat_3 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ X0 )
      | ( v2_tex_2 @ sk_B_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['26','27'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['35','59'])).

thf('61',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['16','60'])).

thf('62',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 @ ( k2_pre_topc @ X38 @ ( sk_C_1 @ X37 @ X38 ) ) )
       != ( sk_C_1 @ X37 @ X38 ) )
      | ( v2_tex_2 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('63',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
     != ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_C_1 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['16','60'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
     != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('75',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('76',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['35','59'])).

thf('81',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['73','81'])).

thf('83',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('84',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X15 @ X14 @ X14 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k9_subset_1 @ X0 @ X1 @ X1 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('90',plain,(
    ! [X13: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X1 )
      = X1 ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['68','82','91'])).

thf('93',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yB9TdWcnmP
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:13:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.11  % Solved by: fo/fo7.sh
% 0.89/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.11  % done 594 iterations in 0.645s
% 0.89/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.11  % SZS output start Refutation
% 0.89/1.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.89/1.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.11  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.89/1.11  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.89/1.11  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.11  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.89/1.11  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.89/1.11  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.89/1.11  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.89/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.11  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.89/1.11  thf(v1_borsuk_1_type, type, v1_borsuk_1: $i > $i > $o).
% 0.89/1.11  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.89/1.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.89/1.11  thf(sk_B_type, type, sk_B: $i > $i).
% 0.89/1.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.89/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.11  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.89/1.11  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.89/1.11  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.89/1.11  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.89/1.11  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.89/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.11  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.89/1.11  thf(t43_tex_2, conjecture,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.89/1.11         ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.89/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.11    (~( ![A:$i]:
% 0.89/1.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.89/1.11            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11          ( ![B:$i]:
% 0.89/1.11            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.89/1.11    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.89/1.11  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('1', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(t41_tex_2, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11           ( ( v2_tex_2 @ B @ A ) <=>
% 0.89/1.11             ( ![C:$i]:
% 0.89/1.11               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11                 ( ( r1_tarski @ C @ B ) =>
% 0.89/1.11                   ( ( k9_subset_1 @
% 0.89/1.11                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 0.89/1.11                     ( C ) ) ) ) ) ) ) ) ))).
% 0.89/1.11  thf('2', plain,
% 0.89/1.11      (![X37 : $i, X38 : $i]:
% 0.89/1.11         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.89/1.11          | (r1_tarski @ (sk_C_1 @ X37 @ X38) @ X37)
% 0.89/1.11          | (v2_tex_2 @ X37 @ X38)
% 0.89/1.11          | ~ (l1_pre_topc @ X38)
% 0.89/1.11          | ~ (v2_pre_topc @ X38)
% 0.89/1.11          | (v2_struct_0 @ X38))),
% 0.89/1.11      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.89/1.11  thf('3', plain,
% 0.89/1.11      (((v2_struct_0 @ sk_A)
% 0.89/1.11        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.89/1.11        | (r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.89/1.11      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.11  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('6', plain,
% 0.89/1.11      (((v2_struct_0 @ sk_A)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.89/1.11        | (r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.89/1.11  thf('7', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('8', plain,
% 0.89/1.11      (((r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('clc', [status(thm)], ['6', '7'])).
% 0.89/1.11  thf('9', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('10', plain, ((r1_tarski @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_B_1)),
% 0.89/1.11      inference('clc', [status(thm)], ['8', '9'])).
% 0.89/1.11  thf(d3_tarski, axiom,
% 0.89/1.11    (![A:$i,B:$i]:
% 0.89/1.11     ( ( r1_tarski @ A @ B ) <=>
% 0.89/1.11       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.89/1.11  thf('11', plain,
% 0.89/1.11      (![X4 : $i, X6 : $i]:
% 0.89/1.11         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.89/1.11      inference('cnf', [status(esa)], [d3_tarski])).
% 0.89/1.11  thf(d1_xboole_0, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.89/1.11  thf('12', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.89/1.11  thf('13', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['11', '12'])).
% 0.89/1.11  thf(d10_xboole_0, axiom,
% 0.89/1.11    (![A:$i,B:$i]:
% 0.89/1.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.11  thf('14', plain,
% 0.89/1.11      (![X7 : $i, X9 : $i]:
% 0.89/1.11         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.89/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.11  thf('15', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['13', '14'])).
% 0.89/1.11  thf('16', plain,
% 0.89/1.11      ((((sk_C_1 @ sk_B_1 @ sk_A) = (sk_B_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.89/1.11      inference('sup-', [status(thm)], ['10', '15'])).
% 0.89/1.11  thf('17', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(t29_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( l1_pre_topc @ A ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.89/1.11  thf('18', plain,
% 0.89/1.11      (![X25 : $i, X26 : $i]:
% 0.89/1.11         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.89/1.11          | ((u1_struct_0 @ (k1_pre_topc @ X26 @ X25)) = (X25))
% 0.89/1.11          | ~ (l1_pre_topc @ X26))),
% 0.89/1.11      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.89/1.11  thf('19', plain,
% 0.89/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['17', '18'])).
% 0.89/1.11  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('21', plain,
% 0.89/1.11      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['19', '20'])).
% 0.89/1.11  thf(fc1_struct_0, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.89/1.11       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.89/1.11  thf('22', plain,
% 0.89/1.11      (![X24 : $i]:
% 0.89/1.11         ((v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.89/1.11          | ~ (l1_struct_0 @ X24)
% 0.89/1.11          | ~ (v2_struct_0 @ X24))),
% 0.89/1.11      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.89/1.11  thf('23', plain,
% 0.89/1.11      (((v1_xboole_0 @ sk_B_1)
% 0.89/1.11        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 0.89/1.11        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['21', '22'])).
% 0.89/1.11  thf('24', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(dt_k1_pre_topc, axiom,
% 0.89/1.11    (![A:$i,B:$i]:
% 0.89/1.11     ( ( ( l1_pre_topc @ A ) & 
% 0.89/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.89/1.11       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.89/1.11         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.89/1.11  thf('25', plain,
% 0.89/1.11      (![X19 : $i, X20 : $i]:
% 0.89/1.11         (~ (l1_pre_topc @ X19)
% 0.89/1.11          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.89/1.11          | (m1_pre_topc @ (k1_pre_topc @ X19 @ X20) @ X19))),
% 0.89/1.11      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.89/1.11  thf('26', plain,
% 0.89/1.11      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.89/1.11      inference('sup-', [status(thm)], ['24', '25'])).
% 0.89/1.11  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('28', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.89/1.11      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.11  thf(dt_m1_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( l1_pre_topc @ A ) =>
% 0.89/1.11       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.89/1.11  thf('29', plain,
% 0.89/1.11      (![X22 : $i, X23 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X22 @ X23)
% 0.89/1.11          | (l1_pre_topc @ X22)
% 0.89/1.11          | ~ (l1_pre_topc @ X23))),
% 0.89/1.11      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.89/1.11  thf('30', plain,
% 0.89/1.11      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['28', '29'])).
% 0.89/1.11  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('32', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['30', '31'])).
% 0.89/1.11  thf(dt_l1_pre_topc, axiom,
% 0.89/1.11    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.89/1.11  thf('33', plain,
% 0.89/1.11      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.89/1.11      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.89/1.11  thf('34', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 0.89/1.11      inference('sup-', [status(thm)], ['32', '33'])).
% 0.89/1.11  thf('35', plain,
% 0.89/1.11      (((v1_xboole_0 @ sk_B_1)
% 0.89/1.11        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 0.89/1.11      inference('demod', [status(thm)], ['23', '34'])).
% 0.89/1.11  thf('36', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('37', plain,
% 0.89/1.11      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['19', '20'])).
% 0.89/1.11  thf(t26_tex_2, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.89/1.11           ( ![C:$i]:
% 0.89/1.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.89/1.11                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.89/1.11  thf('38', plain,
% 0.89/1.11      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.89/1.11         ((v2_struct_0 @ X34)
% 0.89/1.11          | ~ (m1_pre_topc @ X34 @ X35)
% 0.89/1.11          | ((X36) != (u1_struct_0 @ X34))
% 0.89/1.11          | ~ (v1_tdlat_3 @ X34)
% 0.89/1.11          | (v2_tex_2 @ X36 @ X35)
% 0.89/1.11          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.89/1.11          | ~ (l1_pre_topc @ X35)
% 0.89/1.11          | (v2_struct_0 @ X35))),
% 0.89/1.11      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.89/1.11  thf('39', plain,
% 0.89/1.11      (![X34 : $i, X35 : $i]:
% 0.89/1.11         ((v2_struct_0 @ X35)
% 0.89/1.11          | ~ (l1_pre_topc @ X35)
% 0.89/1.11          | ~ (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.89/1.11               (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.89/1.11          | (v2_tex_2 @ (u1_struct_0 @ X34) @ X35)
% 0.89/1.11          | ~ (v1_tdlat_3 @ X34)
% 0.89/1.11          | ~ (m1_pre_topc @ X34 @ X35)
% 0.89/1.11          | (v2_struct_0 @ X34))),
% 0.89/1.11      inference('simplify', [status(thm)], ['38'])).
% 0.89/1.11  thf('40', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.89/1.11          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 0.89/1.11          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.89/1.11          | ~ (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 0.89/1.11          | (v2_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) @ X0)
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | (v2_struct_0 @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['37', '39'])).
% 0.89/1.11  thf('41', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.89/1.11      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.11  thf(cc5_tdlat_3, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.89/1.11         ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_pre_topc @ B @ A ) =>
% 0.89/1.11           ( ( v1_borsuk_1 @ B @ A ) & ( v1_tsep_1 @ B @ A ) & 
% 0.89/1.11             ( v1_tdlat_3 @ B ) ) ) ) ))).
% 0.89/1.11  thf('42', plain,
% 0.89/1.11      (![X32 : $i, X33 : $i]:
% 0.89/1.11         (~ (m1_pre_topc @ X32 @ X33)
% 0.89/1.11          | (v1_tdlat_3 @ X32)
% 0.89/1.11          | ~ (l1_pre_topc @ X33)
% 0.89/1.11          | ~ (v1_tdlat_3 @ X33)
% 0.89/1.11          | ~ (v2_pre_topc @ X33)
% 0.89/1.11          | (v2_struct_0 @ X33))),
% 0.89/1.11      inference('cnf', [status(esa)], [cc5_tdlat_3])).
% 0.89/1.11  thf('43', plain,
% 0.89/1.11      (((v2_struct_0 @ sk_A)
% 0.89/1.11        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.11        | ~ (v1_tdlat_3 @ sk_A)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['41', '42'])).
% 0.89/1.11  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('45', plain, ((v1_tdlat_3 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('47', plain,
% 0.89/1.11      (((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 0.89/1.11      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.89/1.11  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('49', plain, ((v1_tdlat_3 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 0.89/1.11      inference('clc', [status(thm)], ['47', '48'])).
% 0.89/1.11  thf('50', plain,
% 0.89/1.11      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['19', '20'])).
% 0.89/1.11  thf('51', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.89/1.11          | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 0.89/1.11          | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ X0)
% 0.89/1.11          | (v2_tex_2 @ sk_B_1 @ X0)
% 0.89/1.11          | ~ (l1_pre_topc @ X0)
% 0.89/1.11          | (v2_struct_0 @ X0))),
% 0.89/1.11      inference('demod', [status(thm)], ['40', '49', '50'])).
% 0.89/1.11  thf('52', plain,
% 0.89/1.11      (((v2_struct_0 @ sk_A)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.89/1.11        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 0.89/1.11        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['36', '51'])).
% 0.89/1.11  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('54', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.89/1.11      inference('demod', [status(thm)], ['26', '27'])).
% 0.89/1.11  thf('55', plain,
% 0.89/1.11      (((v2_struct_0 @ sk_A)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.89/1.11        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1)))),
% 0.89/1.11      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.89/1.11  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('57', plain,
% 0.89/1.11      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('clc', [status(thm)], ['55', '56'])).
% 0.89/1.11  thf('58', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('59', plain, ((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B_1))),
% 0.89/1.11      inference('clc', [status(thm)], ['57', '58'])).
% 0.89/1.11  thf('60', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.89/1.11      inference('demod', [status(thm)], ['35', '59'])).
% 0.89/1.11  thf('61', plain, (((sk_C_1 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['16', '60'])).
% 0.89/1.11  thf('62', plain,
% 0.89/1.11      (![X37 : $i, X38 : $i]:
% 0.89/1.11         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.89/1.11          | ((k9_subset_1 @ (u1_struct_0 @ X38) @ X37 @ 
% 0.89/1.11              (k2_pre_topc @ X38 @ (sk_C_1 @ X37 @ X38)))
% 0.89/1.11              != (sk_C_1 @ X37 @ X38))
% 0.89/1.11          | (v2_tex_2 @ X37 @ X38)
% 0.89/1.11          | ~ (l1_pre_topc @ X38)
% 0.89/1.11          | ~ (v2_pre_topc @ X38)
% 0.89/1.11          | (v2_struct_0 @ X38))),
% 0.89/1.11      inference('cnf', [status(esa)], [t41_tex_2])).
% 0.89/1.11  thf('63', plain,
% 0.89/1.11      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.89/1.11          (k2_pre_topc @ sk_A @ sk_B_1)) != (sk_C_1 @ sk_B_1 @ sk_A))
% 0.89/1.11        | (v2_struct_0 @ sk_A)
% 0.89/1.11        | ~ (v2_pre_topc @ sk_A)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.89/1.11        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.89/1.11      inference('sup-', [status(thm)], ['61', '62'])).
% 0.89/1.11  thf('64', plain, (((sk_C_1 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['16', '60'])).
% 0.89/1.11  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('67', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('68', plain,
% 0.89/1.11      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ 
% 0.89/1.11          (k2_pre_topc @ sk_A @ sk_B_1)) != (sk_B_1))
% 0.89/1.11        | (v2_struct_0 @ sk_A)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.89/1.11  thf('69', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(t52_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( l1_pre_topc @ A ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.89/1.11             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.89/1.11               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.89/1.11  thf('70', plain,
% 0.89/1.11      (![X27 : $i, X28 : $i]:
% 0.89/1.11         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.89/1.11          | ~ (v4_pre_topc @ X27 @ X28)
% 0.89/1.11          | ((k2_pre_topc @ X28 @ X27) = (X27))
% 0.89/1.11          | ~ (l1_pre_topc @ X28))),
% 0.89/1.11      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.89/1.11  thf('71', plain,
% 0.89/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | ((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.89/1.11        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('sup-', [status(thm)], ['69', '70'])).
% 0.89/1.11  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('73', plain,
% 0.89/1.11      ((((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))
% 0.89/1.11        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('demod', [status(thm)], ['71', '72'])).
% 0.89/1.11  thf('74', plain,
% 0.89/1.11      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf(cc2_pre_topc, axiom,
% 0.89/1.11    (![A:$i]:
% 0.89/1.11     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.89/1.11       ( ![B:$i]:
% 0.89/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.89/1.11           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.89/1.11  thf('75', plain,
% 0.89/1.11      (![X17 : $i, X18 : $i]:
% 0.89/1.11         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.89/1.11          | (v4_pre_topc @ X17 @ X18)
% 0.89/1.11          | ~ (v1_xboole_0 @ X17)
% 0.89/1.11          | ~ (l1_pre_topc @ X18)
% 0.89/1.11          | ~ (v2_pre_topc @ X18))),
% 0.89/1.11      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.89/1.11  thf('76', plain,
% 0.89/1.11      ((~ (v2_pre_topc @ sk_A)
% 0.89/1.11        | ~ (l1_pre_topc @ sk_A)
% 0.89/1.11        | ~ (v1_xboole_0 @ sk_B_1)
% 0.89/1.11        | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('sup-', [status(thm)], ['74', '75'])).
% 0.89/1.11  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('79', plain,
% 0.89/1.11      ((~ (v1_xboole_0 @ sk_B_1) | (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.89/1.11  thf('80', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.89/1.11      inference('demod', [status(thm)], ['35', '59'])).
% 0.89/1.11  thf('81', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.89/1.11      inference('demod', [status(thm)], ['79', '80'])).
% 0.89/1.11  thf('82', plain, (((k2_pre_topc @ sk_A @ sk_B_1) = (sk_B_1))),
% 0.89/1.11      inference('demod', [status(thm)], ['73', '81'])).
% 0.89/1.11  thf('83', plain,
% 0.89/1.11      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.89/1.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.89/1.11  thf(d2_subset_1, axiom,
% 0.89/1.11    (![A:$i,B:$i]:
% 0.89/1.11     ( ( ( v1_xboole_0 @ A ) =>
% 0.89/1.11         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.89/1.11       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.89/1.11         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.89/1.11  thf('84', plain,
% 0.89/1.11      (![X10 : $i, X11 : $i]:
% 0.89/1.11         (~ (r2_hidden @ X10 @ X11)
% 0.89/1.11          | (m1_subset_1 @ X10 @ X11)
% 0.89/1.11          | (v1_xboole_0 @ X11))),
% 0.89/1.11      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.89/1.11  thf('85', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.89/1.11      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.89/1.11  thf('86', plain,
% 0.89/1.11      (![X10 : $i, X11 : $i]:
% 0.89/1.11         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.89/1.11      inference('clc', [status(thm)], ['84', '85'])).
% 0.89/1.11  thf('87', plain,
% 0.89/1.11      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['83', '86'])).
% 0.89/1.11  thf(idempotence_k9_subset_1, axiom,
% 0.89/1.11    (![A:$i,B:$i,C:$i]:
% 0.89/1.11     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.89/1.11       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.89/1.11  thf('88', plain,
% 0.89/1.11      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.11         (((k9_subset_1 @ X15 @ X14 @ X14) = (X14))
% 0.89/1.11          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.89/1.11      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.89/1.11  thf('89', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.89/1.11          | ((k9_subset_1 @ X0 @ X1 @ X1) = (X1)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['87', '88'])).
% 0.89/1.11  thf(fc1_subset_1, axiom,
% 0.89/1.11    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.89/1.11  thf('90', plain, (![X13 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.89/1.11      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.89/1.11  thf('91', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]: ((k9_subset_1 @ X0 @ X1 @ X1) = (X1))),
% 0.89/1.11      inference('clc', [status(thm)], ['89', '90'])).
% 0.89/1.11  thf('92', plain,
% 0.89/1.11      ((((sk_B_1) != (sk_B_1))
% 0.89/1.11        | (v2_struct_0 @ sk_A)
% 0.89/1.11        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.89/1.11      inference('demod', [status(thm)], ['68', '82', '91'])).
% 0.89/1.11  thf('93', plain, (((v2_tex_2 @ sk_B_1 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.89/1.11      inference('simplify', [status(thm)], ['92'])).
% 0.89/1.11  thf('94', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('95', plain, ((v2_struct_0 @ sk_A)),
% 0.89/1.11      inference('clc', [status(thm)], ['93', '94'])).
% 0.89/1.11  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.89/1.11  
% 0.89/1.11  % SZS output end Refutation
% 0.89/1.11  
% 0.89/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

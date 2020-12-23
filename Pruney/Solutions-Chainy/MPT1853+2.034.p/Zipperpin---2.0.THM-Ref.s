%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LS0arAw6pY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:07 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  193 (2410 expanded)
%              Number of leaves         :   38 ( 671 expanded)
%              Depth                    :   25
%              Number of atoms          : 1645 (31545 expanded)
%              Number of equality atoms :   36 ( 284 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('2',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X3 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('16',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('23',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X26 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('32',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','40'])).

thf('42',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('43',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('47',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

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

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( ( sk_C @ X21 @ X22 )
        = ( u1_struct_0 @ X21 ) )
      | ( v1_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('54',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v1_subset_1 @ ( sk_C @ X21 @ X22 ) @ ( u1_struct_0 @ X22 ) )
      | ( v1_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('56',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf('59',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('61',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X37 ) @ X36 ) @ ( u1_struct_0 @ X37 ) )
      | ~ ( v7_struct_0 @ X37 )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('66',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('74',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('75',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65','72','79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['42','86'])).

thf('88',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['41','87'])).

thf(cc1_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ( v1_subset_1 @ B @ A )
           => ( v1_xboole_0 @ B ) ) ) ) )).

thf('89',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_subset_1 @ X19 @ X20 )
      | ~ ( v1_zfmisc_1 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_2])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('94',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X35 @ X34 ) @ X35 )
      | ( v1_zfmisc_1 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_subset_1 @ ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('97',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('98',plain,
    ( ( ( ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('100',plain,
    ( ( ( ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('102',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('103',plain,
    ( ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('105',plain,
    ( ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','107'])).

thf('109',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','108'])).

thf('110',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('111',plain,
    ( ( ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('112',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('113',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('114',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( v1_subset_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X7: $i] :
      ~ ( v1_subset_1 @ X7 @ X7 ) ),
    inference(demod,[status(thm)],['112','117'])).

thf('119',plain,
    ( ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['111','118'])).

thf('120',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['42','86'])).

thf('121',plain,(
    v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['43'])).

thf('123',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('124',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ~ ( v1_tex_2 @ X21 @ X22 )
      | ( X23
       != ( u1_struct_0 @ X21 ) )
      | ( v1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('125',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_tex_2 @ X21 @ X22 )
      | ~ ( m1_pre_topc @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['123','125'])).

thf('127',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['34','35'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','129'])).

thf('131',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('132',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['42','86','131'])).

thf('133',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['130','132'])).

thf('134',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('135',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['42','86'])).

thf('136',plain,
    ( ( k1_tarski @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['133','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['90','121','137'])).

thf('139',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['122','129'])).

thf('140',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('141',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( v1_subset_1 @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['42','86','131'])).

thf('145',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_tarski @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('147',plain,(
    ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['138','147'])).

thf('149',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('150',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('152',plain,(
    v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['6','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LS0arAw6pY
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.78/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.97  % Solved by: fo/fo7.sh
% 0.78/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.97  % done 380 iterations in 0.523s
% 0.78/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.97  % SZS output start Refutation
% 0.78/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.97  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.78/0.97  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.78/0.97  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.78/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.97  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.78/0.97  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.78/0.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.78/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.97  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.78/0.97  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.78/0.97  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.78/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.97  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.78/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.78/0.97  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.78/0.97  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.78/0.97  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.78/0.97  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.78/0.97  thf(sk_B_type, type, sk_B: $i > $i).
% 0.78/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.97  thf(t20_tex_2, conjecture,
% 0.78/0.97    (![A:$i]:
% 0.78/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.78/0.97       ( ![B:$i]:
% 0.78/0.97         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.97           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.78/0.97             ( v1_subset_1 @
% 0.78/0.97               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.78/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.97    (~( ![A:$i]:
% 0.78/0.97        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.78/0.97          ( ![B:$i]:
% 0.78/0.97            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.97              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.78/0.97                ( v1_subset_1 @
% 0.78/0.97                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.78/0.97                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.78/0.97    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.78/0.97  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(dt_k1_tex_2, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.78/0.97         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.97       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.78/0.97         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.78/0.97         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.78/0.97  thf('1', plain,
% 0.78/0.97      (![X26 : $i, X27 : $i]:
% 0.78/0.97         (~ (l1_pre_topc @ X26)
% 0.78/0.97          | (v2_struct_0 @ X26)
% 0.78/0.97          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.78/0.97          | ~ (v2_struct_0 @ (k1_tex_2 @ X26 @ X27)))),
% 0.78/0.97      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.78/0.97  thf('2', plain,
% 0.78/0.97      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.78/0.97        | (v2_struct_0 @ sk_A)
% 0.78/0.97        | ~ (l1_pre_topc @ sk_A))),
% 0.78/0.97      inference('sup-', [status(thm)], ['0', '1'])).
% 0.78/0.97  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('4', plain,
% 0.78/0.97      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['2', '3'])).
% 0.78/0.97  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('6', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.78/0.97      inference('clc', [status(thm)], ['4', '5'])).
% 0.78/0.97  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(d2_subset_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( v1_xboole_0 @ A ) =>
% 0.78/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.78/0.97       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.78/0.97         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.78/0.97  thf('8', plain,
% 0.78/0.97      (![X0 : $i, X1 : $i]:
% 0.78/0.97         (~ (m1_subset_1 @ X0 @ X1)
% 0.78/0.97          | (r2_hidden @ X0 @ X1)
% 0.78/0.97          | (v1_xboole_0 @ X1))),
% 0.78/0.97      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.78/0.97  thf('9', plain,
% 0.78/0.97      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.97        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.78/0.97  thf(t63_subset_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( r2_hidden @ A @ B ) =>
% 0.78/0.97       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.78/0.97  thf('10', plain,
% 0.78/0.97      (![X3 : $i, X4 : $i]:
% 0.78/0.97         ((m1_subset_1 @ (k1_tarski @ X3) @ (k1_zfmisc_1 @ X4))
% 0.78/0.97          | ~ (r2_hidden @ X3 @ X4))),
% 0.78/0.97      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.78/0.97  thf('11', plain,
% 0.78/0.97      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.97        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.78/0.97           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('sup-', [status(thm)], ['9', '10'])).
% 0.78/0.97  thf(d7_subset_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.97       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.78/0.97  thf('12', plain,
% 0.78/0.97      (![X24 : $i, X25 : $i]:
% 0.78/0.97         (((X25) = (X24))
% 0.78/0.97          | (v1_subset_1 @ X25 @ X24)
% 0.78/0.97          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.78/0.97  thf('13', plain,
% 0.78/0.97      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.97        | (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.78/0.97        | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['11', '12'])).
% 0.78/0.97  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(redefinition_k6_domain_1, axiom,
% 0.78/0.97    (![A:$i,B:$i]:
% 0.78/0.97     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.78/0.97       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.78/0.97  thf('15', plain,
% 0.78/0.97      (![X17 : $i, X18 : $i]:
% 0.78/0.97         ((v1_xboole_0 @ X17)
% 0.78/0.97          | ~ (m1_subset_1 @ X18 @ X17)
% 0.78/0.97          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.78/0.97      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.78/0.97  thf('16', plain,
% 0.78/0.97      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.78/0.97        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['14', '15'])).
% 0.78/0.97  thf('17', plain,
% 0.78/0.97      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97           (u1_struct_0 @ sk_A))
% 0.78/0.97        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('18', plain,
% 0.78/0.97      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97           (u1_struct_0 @ sk_A)))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('split', [status(esa)], ['17'])).
% 0.78/0.97  thf('19', plain,
% 0.78/0.97      (((~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.78/0.97         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('sup-', [status(thm)], ['16', '18'])).
% 0.78/0.97  thf('20', plain,
% 0.78/0.97      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.78/0.97         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.97         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('sup-', [status(thm)], ['13', '19'])).
% 0.78/0.97  thf('21', plain,
% 0.78/0.97      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.97         | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('simplify', [status(thm)], ['20'])).
% 0.78/0.97  thf(fc2_struct_0, axiom,
% 0.78/0.97    (![A:$i]:
% 0.78/0.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.78/0.97       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.78/0.97  thf('22', plain,
% 0.78/0.97      (![X16 : $i]:
% 0.78/0.97         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.78/0.97          | ~ (l1_struct_0 @ X16)
% 0.78/0.97          | (v2_struct_0 @ X16))),
% 0.78/0.97      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.78/0.97  thf('23', plain,
% 0.78/0.97      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.78/0.97         | (v2_struct_0 @ sk_A)
% 0.78/0.97         | ~ (l1_struct_0 @ sk_A)))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('sup-', [status(thm)], ['21', '22'])).
% 0.78/0.97  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf(dt_l1_pre_topc, axiom,
% 0.78/0.97    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.78/0.97  thf('25', plain,
% 0.78/0.97      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.78/0.97      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.78/0.97  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.78/0.97      inference('sup-', [status(thm)], ['24', '25'])).
% 0.78/0.97  thf('27', plain,
% 0.78/0.97      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('demod', [status(thm)], ['23', '26'])).
% 0.78/0.97  thf('28', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('29', plain,
% 0.78/0.97      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('clc', [status(thm)], ['27', '28'])).
% 0.78/0.97  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('31', plain,
% 0.78/0.97      (![X26 : $i, X27 : $i]:
% 0.78/0.97         (~ (l1_pre_topc @ X26)
% 0.78/0.97          | (v2_struct_0 @ X26)
% 0.78/0.97          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.78/0.97          | (m1_pre_topc @ (k1_tex_2 @ X26 @ X27) @ X26))),
% 0.78/0.97      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.78/0.97  thf('32', plain,
% 0.78/0.97      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97        | (v2_struct_0 @ sk_A)
% 0.78/0.97        | ~ (l1_pre_topc @ sk_A))),
% 0.78/0.97      inference('sup-', [status(thm)], ['30', '31'])).
% 0.78/0.97  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('34', plain,
% 0.78/0.97      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97        | (v2_struct_0 @ sk_A))),
% 0.78/0.97      inference('demod', [status(thm)], ['32', '33'])).
% 0.78/0.97  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('36', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.78/0.97      inference('clc', [status(thm)], ['34', '35'])).
% 0.78/0.97  thf(l17_tex_2, axiom,
% 0.78/0.97    (![A:$i]:
% 0.78/0.97     ( ( l1_pre_topc @ A ) =>
% 0.78/0.97       ( ![B:$i]:
% 0.78/0.97         ( ( m1_pre_topc @ B @ A ) =>
% 0.78/0.97           ( m1_subset_1 @
% 0.78/0.97             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.78/0.97  thf('37', plain,
% 0.78/0.97      (![X30 : $i, X31 : $i]:
% 0.78/0.97         (~ (m1_pre_topc @ X30 @ X31)
% 0.78/0.97          | (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 0.78/0.97             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.78/0.97          | ~ (l1_pre_topc @ X31))),
% 0.78/0.97      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.78/0.97  thf('38', plain,
% 0.78/0.97      ((~ (l1_pre_topc @ sk_A)
% 0.78/0.97        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.97           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('sup-', [status(thm)], ['36', '37'])).
% 0.78/0.97  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('40', plain,
% 0.78/0.97      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.97      inference('demod', [status(thm)], ['38', '39'])).
% 0.78/0.97  thf('41', plain,
% 0.78/0.97      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.97         (k1_zfmisc_1 @ (k1_tarski @ sk_B_1))))
% 0.78/0.97         <= (~
% 0.78/0.97             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('sup+', [status(thm)], ['29', '40'])).
% 0.78/0.97  thf('42', plain,
% 0.78/0.97      (~
% 0.78/0.97       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97         (u1_struct_0 @ sk_A))) | 
% 0.78/0.97       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.78/0.97      inference('split', [status(esa)], ['17'])).
% 0.78/0.97  thf('43', plain,
% 0.78/0.97      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97         (u1_struct_0 @ sk_A))
% 0.78/0.97        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('44', plain,
% 0.78/0.97      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97         (u1_struct_0 @ sk_A)))
% 0.78/0.97         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.97               (u1_struct_0 @ sk_A))))),
% 0.78/0.97      inference('split', [status(esa)], ['43'])).
% 0.78/0.97  thf('45', plain,
% 0.78/0.97      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.97        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.97      inference('demod', [status(thm)], ['38', '39'])).
% 0.78/0.97  thf('46', plain,
% 0.78/0.97      (![X24 : $i, X25 : $i]:
% 0.78/0.97         (((X25) = (X24))
% 0.78/0.97          | (v1_subset_1 @ X25 @ X24)
% 0.78/0.97          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.78/0.97      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.78/0.97  thf('47', plain,
% 0.78/0.97      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.97         (u1_struct_0 @ sk_A))
% 0.78/0.97        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['45', '46'])).
% 0.78/0.97  thf('48', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.78/0.97      inference('clc', [status(thm)], ['34', '35'])).
% 0.78/0.97  thf(d3_tex_2, axiom,
% 0.78/0.97    (![A:$i]:
% 0.78/0.97     ( ( l1_pre_topc @ A ) =>
% 0.78/0.97       ( ![B:$i]:
% 0.78/0.97         ( ( m1_pre_topc @ B @ A ) =>
% 0.78/0.97           ( ( v1_tex_2 @ B @ A ) <=>
% 0.78/0.97             ( ![C:$i]:
% 0.78/0.97               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.97                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.78/0.97                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.78/0.97  thf('49', plain,
% 0.78/0.97      (![X21 : $i, X22 : $i]:
% 0.78/0.97         (~ (m1_pre_topc @ X21 @ X22)
% 0.78/0.97          | ((sk_C @ X21 @ X22) = (u1_struct_0 @ X21))
% 0.78/0.97          | (v1_tex_2 @ X21 @ X22)
% 0.78/0.97          | ~ (l1_pre_topc @ X22))),
% 0.78/0.97      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.78/0.97  thf('50', plain,
% 0.78/0.97      ((~ (l1_pre_topc @ sk_A)
% 0.78/0.97        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.78/0.97      inference('sup-', [status(thm)], ['48', '49'])).
% 0.78/0.97  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.97  thf('52', plain,
% 0.78/0.97      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.78/0.97      inference('demod', [status(thm)], ['50', '51'])).
% 0.78/0.97  thf('53', plain,
% 0.78/0.97      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.78/0.97         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.97      inference('split', [status(esa)], ['17'])).
% 0.78/0.97  thf('54', plain,
% 0.78/0.97      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.78/0.97         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['52', '53'])).
% 0.78/0.97  thf('55', plain,
% 0.78/0.97      (![X21 : $i, X22 : $i]:
% 0.78/0.97         (~ (m1_pre_topc @ X21 @ X22)
% 0.78/0.97          | ~ (v1_subset_1 @ (sk_C @ X21 @ X22) @ (u1_struct_0 @ X22))
% 0.78/0.97          | (v1_tex_2 @ X21 @ X22)
% 0.78/0.97          | ~ (l1_pre_topc @ X22))),
% 0.78/0.97      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.78/0.97  thf('56', plain,
% 0.78/0.97      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.97            (u1_struct_0 @ sk_A))
% 0.78/0.97         | ~ (l1_pre_topc @ sk_A)
% 0.78/0.97         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.97         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.78/0.97         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.97      inference('sup-', [status(thm)], ['54', '55'])).
% 0.78/0.97  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('58', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.78/0.98      inference('clc', [status(thm)], ['34', '35'])).
% 0.78/0.98  thf('59', plain,
% 0.78/0.98      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98            (u1_struct_0 @ sk_A))
% 0.78/0.98         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.78/0.98  thf('60', plain,
% 0.78/0.98      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('split', [status(esa)], ['17'])).
% 0.78/0.98  thf('61', plain,
% 0.78/0.98      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98           (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('clc', [status(thm)], ['59', '60'])).
% 0.78/0.98  thf('62', plain,
% 0.78/0.98      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['47', '61'])).
% 0.78/0.98  thf(t8_tex_2, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.78/0.98       ( ![B:$i]:
% 0.78/0.98         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.78/0.98           ( ~( ( v1_subset_1 @
% 0.78/0.98                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.78/0.98                  ( u1_struct_0 @ A ) ) & 
% 0.78/0.98                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.78/0.98  thf('63', plain,
% 0.78/0.98      (![X36 : $i, X37 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 0.78/0.98          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X37) @ X36) @ 
% 0.78/0.98               (u1_struct_0 @ X37))
% 0.78/0.98          | ~ (v7_struct_0 @ X37)
% 0.78/0.98          | ~ (l1_struct_0 @ X37)
% 0.78/0.98          | (v2_struct_0 @ X37))),
% 0.78/0.98      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.78/0.98  thf('64', plain,
% 0.78/0.98      ((![X0 : $i]:
% 0.78/0.98          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.78/0.98              (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.78/0.98           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.78/0.98           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.78/0.98           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.78/0.98           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['62', '63'])).
% 0.78/0.98  thf('65', plain,
% 0.78/0.98      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['47', '61'])).
% 0.78/0.98  thf('66', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.78/0.98      inference('clc', [status(thm)], ['34', '35'])).
% 0.78/0.98  thf(dt_m1_pre_topc, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( l1_pre_topc @ A ) =>
% 0.78/0.98       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.78/0.98  thf('67', plain,
% 0.78/0.98      (![X12 : $i, X13 : $i]:
% 0.78/0.98         (~ (m1_pre_topc @ X12 @ X13)
% 0.78/0.98          | (l1_pre_topc @ X12)
% 0.78/0.98          | ~ (l1_pre_topc @ X13))),
% 0.78/0.98      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.78/0.98  thf('68', plain,
% 0.78/0.98      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['66', '67'])).
% 0.78/0.98  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('70', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['68', '69'])).
% 0.78/0.98  thf('71', plain,
% 0.78/0.98      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.78/0.98      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.78/0.98  thf('72', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['70', '71'])).
% 0.78/0.98  thf('73', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(fc2_tex_2, axiom,
% 0.78/0.98    (![A:$i,B:$i]:
% 0.78/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.78/0.98         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.78/0.98       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.78/0.98         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.78/0.98         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.78/0.98  thf('74', plain,
% 0.78/0.98      (![X28 : $i, X29 : $i]:
% 0.78/0.98         (~ (l1_pre_topc @ X28)
% 0.78/0.98          | (v2_struct_0 @ X28)
% 0.78/0.98          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.78/0.98          | (v7_struct_0 @ (k1_tex_2 @ X28 @ X29)))),
% 0.78/0.98      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.78/0.98  thf('75', plain,
% 0.78/0.98      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.78/0.98        | (v2_struct_0 @ sk_A)
% 0.78/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.78/0.98      inference('sup-', [status(thm)], ['73', '74'])).
% 0.78/0.98  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('77', plain,
% 0.78/0.98      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.78/0.98      inference('demod', [status(thm)], ['75', '76'])).
% 0.78/0.98  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('79', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('clc', [status(thm)], ['77', '78'])).
% 0.78/0.98  thf('80', plain,
% 0.78/0.98      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['47', '61'])).
% 0.78/0.98  thf('81', plain,
% 0.78/0.98      ((![X0 : $i]:
% 0.78/0.98          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.78/0.98              (u1_struct_0 @ sk_A))
% 0.78/0.98           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.78/0.98           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['64', '65', '72', '79', '80'])).
% 0.78/0.98  thf('82', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('clc', [status(thm)], ['4', '5'])).
% 0.78/0.98  thf('83', plain,
% 0.78/0.98      ((![X0 : $i]:
% 0.78/0.98          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.78/0.98           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.78/0.98                (u1_struct_0 @ sk_A))))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('clc', [status(thm)], ['81', '82'])).
% 0.78/0.98  thf('84', plain,
% 0.78/0.98      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('sup-', [status(thm)], ['44', '83'])).
% 0.78/0.98  thf('85', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('86', plain,
% 0.78/0.98      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.78/0.98       ~
% 0.78/0.98       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98         (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['84', '85'])).
% 0.78/0.98  thf('87', plain,
% 0.78/0.98      (~
% 0.78/0.98       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98         (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('sat_resolution*', [status(thm)], ['42', '86'])).
% 0.78/0.98  thf('88', plain,
% 0.78/0.98      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98        (k1_zfmisc_1 @ (k1_tarski @ sk_B_1)))),
% 0.78/0.98      inference('simpl_trail', [status(thm)], ['41', '87'])).
% 0.78/0.98  thf(cc1_tex_2, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.78/0.98       ( ![B:$i]:
% 0.78/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.98           ( ( v1_subset_1 @ B @ A ) => ( v1_xboole_0 @ B ) ) ) ) ))).
% 0.78/0.98  thf('89', plain,
% 0.78/0.98      (![X19 : $i, X20 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.78/0.98          | (v1_xboole_0 @ X19)
% 0.78/0.98          | ~ (v1_subset_1 @ X19 @ X20)
% 0.78/0.98          | ~ (v1_zfmisc_1 @ X20)
% 0.78/0.98          | (v1_xboole_0 @ X20))),
% 0.78/0.98      inference('cnf', [status(esa)], [cc1_tex_2])).
% 0.78/0.98  thf('90', plain,
% 0.78/0.98      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.78/0.98        | ~ (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.78/0.98        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98             (k1_tarski @ sk_B_1))
% 0.78/0.98        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.78/0.98      inference('sup-', [status(thm)], ['88', '89'])).
% 0.78/0.98  thf('91', plain,
% 0.78/0.98      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['27', '28'])).
% 0.78/0.98  thf('92', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('93', plain,
% 0.78/0.98      (((m1_subset_1 @ sk_B_1 @ (k1_tarski @ sk_B_1)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('sup+', [status(thm)], ['91', '92'])).
% 0.78/0.98  thf(t7_tex_2, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.78/0.98       ( ![B:$i]:
% 0.78/0.98         ( ( m1_subset_1 @ B @ A ) =>
% 0.78/0.98           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.78/0.98  thf('94', plain,
% 0.78/0.98      (![X34 : $i, X35 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X34 @ X35)
% 0.78/0.98          | (v1_subset_1 @ (k6_domain_1 @ X35 @ X34) @ X35)
% 0.78/0.98          | (v1_zfmisc_1 @ X35)
% 0.78/0.98          | (v1_xboole_0 @ X35))),
% 0.78/0.98      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.78/0.98  thf('95', plain,
% 0.78/0.98      ((((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v1_subset_1 @ (k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1) @ 
% 0.78/0.98            (k1_tarski @ sk_B_1))))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('sup-', [status(thm)], ['93', '94'])).
% 0.78/0.98  thf('96', plain,
% 0.78/0.98      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['27', '28'])).
% 0.78/0.98  thf('97', plain,
% 0.78/0.98      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.78/0.98        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['14', '15'])).
% 0.78/0.98  thf('98', plain,
% 0.78/0.98      (((((k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('sup+', [status(thm)], ['96', '97'])).
% 0.78/0.98  thf('99', plain,
% 0.78/0.98      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['27', '28'])).
% 0.78/0.98  thf('100', plain,
% 0.78/0.98      (((((k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('demod', [status(thm)], ['98', '99'])).
% 0.78/0.98  thf('101', plain,
% 0.78/0.98      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['27', '28'])).
% 0.78/0.98  thf('102', plain,
% 0.78/0.98      (![X16 : $i]:
% 0.78/0.98         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.78/0.98          | ~ (l1_struct_0 @ X16)
% 0.78/0.98          | (v2_struct_0 @ X16))),
% 0.78/0.98      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.78/0.98  thf('103', plain,
% 0.78/0.98      (((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v2_struct_0 @ sk_A)
% 0.78/0.98         | ~ (l1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('sup-', [status(thm)], ['101', '102'])).
% 0.78/0.98  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 0.78/0.98      inference('sup-', [status(thm)], ['24', '25'])).
% 0.78/0.98  thf('105', plain,
% 0.78/0.98      (((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1)) | (v2_struct_0 @ sk_A)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('demod', [status(thm)], ['103', '104'])).
% 0.78/0.98  thf('106', plain, (~ (v2_struct_0 @ sk_A)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('107', plain,
% 0.78/0.98      ((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['105', '106'])).
% 0.78/0.98  thf('108', plain,
% 0.78/0.98      ((((k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1) = (k1_tarski @ sk_B_1)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['100', '107'])).
% 0.78/0.98  thf('109', plain,
% 0.78/0.98      ((((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('demod', [status(thm)], ['95', '108'])).
% 0.78/0.98  thf('110', plain,
% 0.78/0.98      ((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['105', '106'])).
% 0.78/0.98  thf('111', plain,
% 0.78/0.98      ((((v1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_tarski @ sk_B_1))
% 0.78/0.98         | (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['109', '110'])).
% 0.78/0.98  thf(rc3_subset_1, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ?[B:$i]:
% 0.78/0.98       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.78/0.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.78/0.98  thf('112', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.78/0.98      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.78/0.98  thf('113', plain,
% 0.78/0.98      (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.78/0.98      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.78/0.98  thf('114', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i]:
% 0.78/0.98         (((X25) = (X24))
% 0.78/0.98          | (v1_subset_1 @ X25 @ X24)
% 0.78/0.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.78/0.98      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.78/0.98  thf('115', plain,
% 0.78/0.98      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['113', '114'])).
% 0.78/0.98  thf('116', plain, (![X7 : $i]: ~ (v1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.78/0.98      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.78/0.98  thf('117', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.78/0.98      inference('clc', [status(thm)], ['115', '116'])).
% 0.78/0.98  thf('118', plain, (![X7 : $i]: ~ (v1_subset_1 @ X7 @ X7)),
% 0.78/0.98      inference('demod', [status(thm)], ['112', '117'])).
% 0.78/0.98  thf('119', plain,
% 0.78/0.98      (((v1_zfmisc_1 @ (k1_tarski @ sk_B_1)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['111', '118'])).
% 0.78/0.98  thf('120', plain,
% 0.78/0.98      (~
% 0.78/0.98       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98         (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('sat_resolution*', [status(thm)], ['42', '86'])).
% 0.78/0.98  thf('121', plain, ((v1_zfmisc_1 @ (k1_tarski @ sk_B_1))),
% 0.78/0.98      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 0.78/0.98  thf('122', plain,
% 0.78/0.98      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.78/0.98         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('split', [status(esa)], ['43'])).
% 0.78/0.98  thf('123', plain,
% 0.78/0.98      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['38', '39'])).
% 0.78/0.98  thf('124', plain,
% 0.78/0.98      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.78/0.98         (~ (m1_pre_topc @ X21 @ X22)
% 0.78/0.98          | ~ (v1_tex_2 @ X21 @ X22)
% 0.78/0.98          | ((X23) != (u1_struct_0 @ X21))
% 0.78/0.98          | (v1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.78/0.98          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.78/0.98          | ~ (l1_pre_topc @ X22))),
% 0.78/0.98      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.78/0.98  thf('125', plain,
% 0.78/0.98      (![X21 : $i, X22 : $i]:
% 0.78/0.98         (~ (l1_pre_topc @ X22)
% 0.78/0.98          | ~ (m1_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.78/0.98               (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.78/0.98          | (v1_subset_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X22))
% 0.78/0.98          | ~ (v1_tex_2 @ X21 @ X22)
% 0.78/0.98          | ~ (m1_pre_topc @ X21 @ X22))),
% 0.78/0.98      inference('simplify', [status(thm)], ['124'])).
% 0.78/0.98  thf('126', plain,
% 0.78/0.98      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.98        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.98        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98           (u1_struct_0 @ sk_A))
% 0.78/0.98        | ~ (l1_pre_topc @ sk_A))),
% 0.78/0.98      inference('sup-', [status(thm)], ['123', '125'])).
% 0.78/0.98  thf('127', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.78/0.98      inference('clc', [status(thm)], ['34', '35'])).
% 0.78/0.98  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('129', plain,
% 0.78/0.98      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.78/0.98        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98           (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.78/0.98  thf('130', plain,
% 0.78/0.98      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98         (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['122', '129'])).
% 0.78/0.98  thf('131', plain,
% 0.78/0.98      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.78/0.98       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98         (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('split', [status(esa)], ['43'])).
% 0.78/0.98  thf('132', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.78/0.98      inference('sat_resolution*', [status(thm)], ['42', '86', '131'])).
% 0.78/0.98  thf('133', plain,
% 0.78/0.98      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98        (u1_struct_0 @ sk_A))),
% 0.78/0.98      inference('simpl_trail', [status(thm)], ['130', '132'])).
% 0.78/0.98  thf('134', plain,
% 0.78/0.98      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (~
% 0.78/0.98             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98               (u1_struct_0 @ sk_A))))),
% 0.78/0.98      inference('clc', [status(thm)], ['27', '28'])).
% 0.78/0.98  thf('135', plain,
% 0.78/0.98      (~
% 0.78/0.98       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.78/0.98         (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('sat_resolution*', [status(thm)], ['42', '86'])).
% 0.78/0.98  thf('136', plain, (((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.78/0.98      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 0.78/0.98  thf('137', plain,
% 0.78/0.98      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98        (k1_tarski @ sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['133', '136'])).
% 0.78/0.98  thf('138', plain,
% 0.78/0.98      (((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.78/0.98        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.78/0.98      inference('demod', [status(thm)], ['90', '121', '137'])).
% 0.78/0.98  thf('139', plain,
% 0.78/0.98      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98         (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['122', '129'])).
% 0.78/0.98  thf('140', plain,
% 0.78/0.98      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['38', '39'])).
% 0.78/0.98  thf(cc4_subset_1, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( v1_xboole_0 @ A ) =>
% 0.78/0.98       ( ![B:$i]:
% 0.78/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.78/0.98           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.78/0.98  thf('141', plain,
% 0.78/0.98      (![X5 : $i, X6 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.78/0.98          | ~ (v1_subset_1 @ X5 @ X6)
% 0.78/0.98          | ~ (v1_xboole_0 @ X6))),
% 0.78/0.98      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.78/0.98  thf('142', plain,
% 0.78/0.98      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.78/0.98        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.78/0.98             (u1_struct_0 @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['140', '141'])).
% 0.78/0.98  thf('143', plain,
% 0.78/0.98      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.78/0.98         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['139', '142'])).
% 0.78/0.98  thf('144', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.78/0.98      inference('sat_resolution*', [status(thm)], ['42', '86', '131'])).
% 0.78/0.98  thf('145', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.78/0.98      inference('simpl_trail', [status(thm)], ['143', '144'])).
% 0.78/0.98  thf('146', plain, (((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.78/0.98      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 0.78/0.98  thf('147', plain, (~ (v1_xboole_0 @ (k1_tarski @ sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['145', '146'])).
% 0.78/0.98  thf('148', plain,
% 0.78/0.98      ((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.78/0.98      inference('clc', [status(thm)], ['138', '147'])).
% 0.78/0.98  thf('149', plain,
% 0.78/0.98      (![X16 : $i]:
% 0.78/0.98         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.78/0.98          | ~ (l1_struct_0 @ X16)
% 0.78/0.98          | (v2_struct_0 @ X16))),
% 0.78/0.98      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.78/0.98  thf('150', plain,
% 0.78/0.98      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.78/0.98        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['148', '149'])).
% 0.78/0.98  thf('151', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['70', '71'])).
% 0.78/0.98  thf('152', plain, ((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['150', '151'])).
% 0.78/0.98  thf('153', plain, ($false), inference('demod', [status(thm)], ['6', '152'])).
% 0.78/0.98  
% 0.78/0.98  % SZS output end Refutation
% 0.78/0.98  
% 0.78/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

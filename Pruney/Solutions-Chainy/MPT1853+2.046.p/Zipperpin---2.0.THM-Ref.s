%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6VUtEISSql

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 (1071 expanded)
%              Number of leaves         :   36 ( 301 expanded)
%              Depth                    :   22
%              Number of atoms          : 1485 (13419 expanded)
%              Number of equality atoms :   64 ( 260 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

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

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X35 @ X34 ) @ X35 )
      | ( v1_zfmisc_1 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('7',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i] :
      ( ~ ( v1_zfmisc_1 @ X20 )
      | ( X20
        = ( k6_domain_1 @ X20 @ ( sk_B @ X20 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('18',plain,(
    ! [X20: $i] :
      ( ~ ( v1_zfmisc_1 @ X20 )
      | ( m1_subset_1 @ ( sk_B @ X20 ) @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('25',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','26'])).

thf('28',plain,
    ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_1
      = ( sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('31',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('33',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('36',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('38',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('43',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( X27
       != ( k1_tex_2 @ X26 @ X25 ) )
      | ( ( u1_struct_0 @ X27 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X25 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( v1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X26 @ X25 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X26 @ X25 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X26 @ X25 ) @ X26 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X26 @ X25 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X26 ) @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('54',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X28 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('63',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['60','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['40','70'])).

thf('72',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_1
        = ( sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','28'])).

thf('73',plain,(
    ! [X20: $i] :
      ( ~ ( v1_zfmisc_1 @ X20 )
      | ( X20
        = ( k6_domain_1 @ X20 @ ( sk_B @ X20 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('74',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('76',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('79',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('81',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('83',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('84',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('85',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('86',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('87',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','89'])).

thf('91',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','90'])).

thf('92',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('93',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('94',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['94'])).

thf('96',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['93','95'])).

thf('97',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

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

thf('98',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( sk_C_1 @ X22 @ X23 )
        = ( u1_struct_0 @ X22 ) )
      | ( v1_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('103',plain,
    ( ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ( v1_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('105',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('108',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('110',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','110'])).

thf('112',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['92','111'])).

thf('113',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['91','112'])).

thf('114',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf(t15_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ~ ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( v1_tex_2 @ B @ A ) ) ) ) )).

thf('115',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( ( u1_struct_0 @ X30 )
       != ( u1_struct_0 @ X31 ) )
      | ~ ( v1_tex_2 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t15_tex_2])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ X0 )
         != ( k1_tarski @ sk_B_1 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v1_tex_2 @ X0 @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ! [X0: $i] :
        ( ( ( u1_struct_0 @ X0 )
         != ( k1_tarski @ sk_B_1 ) )
        | ~ ( v1_tex_2 @ X0 @ sk_A )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['92','111'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k1_tarski @ sk_B_1 )
     != ( k1_tarski @ sk_B_1 ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['113','120'])).

thf('122',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['56','57'])).

thf('123',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['94'])).

thf('124',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['94'])).

thf('125',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['92','111','124'])).

thf('126',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['123','125'])).

thf('127',plain,(
    ( k1_tarski @ sk_B_1 )
 != ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['121','122','126'])).

thf('128',plain,(
    $false ),
    inference(simplify,[status(thm)],['127'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6VUtEISSql
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 212 iterations in 0.086s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.54  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.21/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.54  thf(t20_tex_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.54             ( v1_subset_1 @
% 0.21/0.54               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.21/0.54                ( v1_subset_1 @
% 0.21/0.54                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.54                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.21/0.54  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t7_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.54           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X34 : $i, X35 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X34 @ X35)
% 0.21/0.54          | (v1_subset_1 @ (k6_domain_1 @ X35 @ X34) @ X35)
% 0.21/0.54          | (v1_zfmisc_1 @ X35)
% 0.21/0.54          | (v1_xboole_0 @ X35))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A))
% 0.21/0.54        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '4'])).
% 0.21/0.54  thf(fc2_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.54       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X17 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.21/0.54          | ~ (l1_struct_0 @ X17)
% 0.21/0.54          | (v2_struct_0 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v2_struct_0 @ sk_A)
% 0.21/0.54         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.54  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_l1_pre_topc, axiom,
% 0.21/0.54    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.54  thf('9', plain, (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.54  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['7', '10'])).
% 0.21/0.54  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('14', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t2_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i]:
% 0.21/0.54         ((r2_hidden @ X8 @ X9)
% 0.21/0.54          | (v1_xboole_0 @ X9)
% 0.21/0.54          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.54  thf(d1_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ( v1_zfmisc_1 @ A ) <=>
% 0.21/0.54         ( ?[B:$i]:
% 0.21/0.54           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X20 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X20)
% 0.21/0.54          | ((X20) = (k6_domain_1 @ X20 @ (sk_B @ X20)))
% 0.21/0.54          | (v1_xboole_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X20 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X20)
% 0.21/0.54          | (m1_subset_1 @ (sk_B @ X20) @ X20)
% 0.21/0.54          | (v1_xboole_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X18)
% 0.21/0.54          | ~ (m1_subset_1 @ X19 @ X18)
% 0.21/0.54          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.54          | (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['17', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.54  thf(d1_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i, X3 : $i]:
% 0.21/0.54         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | ((X1) = (sk_B @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((sk_B_1) = (sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['16', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      ((~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((sk_B_1) = (sk_B @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ((sk_B_1) = (sk_B @ (u1_struct_0 @ sk_A)))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '28'])).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X0)
% 0.21/0.54          | (v1_xboole_0 @ X0)
% 0.21/0.54          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X17 : $i]:
% 0.21/0.54         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 0.21/0.54          | ~ (l1_struct_0 @ X17)
% 0.21/0.54          | (v2_struct_0 @ X17))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1))
% 0.21/0.54         | (v2_struct_0 @ sk_A)
% 0.21/0.54         | ~ (l1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.54  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1)) | (v2_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k1_tex_2, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.21/0.54         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.21/0.54         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X28)
% 0.21/0.54          | (v2_struct_0 @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.21/0.54          | (v1_pre_topc @ (k1_tex_2 @ X28 @ X29)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.54  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('47', plain, ((v1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf(d4_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.21/0.54                 ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.54               ( ( ( C ) = ( k1_tex_2 @ A @ B ) ) <=>
% 0.21/0.54                 ( ( u1_struct_0 @ C ) =
% 0.21/0.54                   ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 0.21/0.54          | ((X27) != (k1_tex_2 @ X26 @ X25))
% 0.21/0.54          | ((u1_struct_0 @ X27) = (k6_domain_1 @ (u1_struct_0 @ X26) @ X25))
% 0.21/0.54          | ~ (m1_pre_topc @ X27 @ X26)
% 0.21/0.54          | ~ (v1_pre_topc @ X27)
% 0.21/0.54          | (v2_struct_0 @ X27)
% 0.21/0.54          | ~ (l1_pre_topc @ X26)
% 0.21/0.54          | (v2_struct_0 @ X26))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_tex_2])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X25 : $i, X26 : $i]:
% 0.21/0.54         ((v2_struct_0 @ X26)
% 0.21/0.54          | ~ (l1_pre_topc @ X26)
% 0.21/0.54          | (v2_struct_0 @ (k1_tex_2 @ X26 @ X25))
% 0.21/0.54          | ~ (v1_pre_topc @ (k1_tex_2 @ X26 @ X25))
% 0.21/0.54          | ~ (m1_pre_topc @ (k1_tex_2 @ X26 @ X25) @ X26)
% 0.21/0.54          | ((u1_struct_0 @ (k1_tex_2 @ X26 @ X25))
% 0.21/0.54              = (k6_domain_1 @ (u1_struct_0 @ X26) @ X25))
% 0.21/0.54          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.54        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.54        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.54  thf('51', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('52', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X28)
% 0.21/0.54          | (v2_struct_0 @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.21/0.54          | (m1_pre_topc @ (k1_tex_2 @ X28 @ X29) @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.54  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('58', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('60', plain,
% 0.21/0.54      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54          = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['50', '51', '58', '59'])).
% 0.21/0.54  thf('61', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('62', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X28)
% 0.21/0.54          | (v2_struct_0 @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X28))
% 0.21/0.54          | ~ (v2_struct_0 @ (k1_tex_2 @ X28 @ X29)))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.21/0.54  thf('63', plain,
% 0.21/0.54      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54        | (v2_struct_0 @ sk_A)
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.54  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('65', plain,
% 0.21/0.54      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.54  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('67', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.54  thf('68', plain,
% 0.21/0.54      (((v2_struct_0 @ sk_A)
% 0.21/0.54        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54            = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.21/0.54      inference('clc', [status(thm)], ['60', '67'])).
% 0.21/0.54  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('70', plain,
% 0.21/0.54      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('71', plain,
% 0.21/0.54      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54          = (k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['40', '70'])).
% 0.21/0.54  thf('72', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ((sk_B_1) = (sk_B @ (u1_struct_0 @ sk_A)))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '28'])).
% 0.21/0.54  thf('73', plain,
% 0.21/0.54      (![X20 : $i]:
% 0.21/0.54         (~ (v1_zfmisc_1 @ X20)
% 0.21/0.54          | ((X20) = (k6_domain_1 @ X20 @ (sk_B @ X20)))
% 0.21/0.54          | (v1_xboole_0 @ X20))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.21/0.54  thf('74', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['72', '73'])).
% 0.21/0.54  thf('75', plain,
% 0.21/0.54      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.54  thf('76', plain,
% 0.21/0.54      (((((u1_struct_0 @ sk_A) = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['74', '75'])).
% 0.21/0.54  thf('77', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.54         | ((u1_struct_0 @ sk_A)
% 0.21/0.54             = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.54  thf('78', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('79', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('80', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('81', plain,
% 0.21/0.54      ((((v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.21/0.54         | ((k1_tarski @ sk_B_1)
% 0.21/0.54             = (k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1))))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.21/0.54  thf('82', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.54         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.54  thf('83', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['82'])).
% 0.21/0.54  thf(dt_k2_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.54  thf('84', plain,
% 0.21/0.54      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.54  thf('85', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.54  thf('86', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.21/0.54      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.54  thf(t5_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.21/0.54          ( v1_xboole_0 @ C ) ) ))).
% 0.21/0.54  thf('87', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X10 @ X11)
% 0.21/0.54          | ~ (v1_xboole_0 @ X12)
% 0.21/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t5_subset])).
% 0.21/0.54  thf('88', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.54  thf('89', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['83', '88'])).
% 0.21/0.54  thf('90', plain,
% 0.21/0.54      ((((k1_tarski @ sk_B_1) = (k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['81', '89'])).
% 0.21/0.54  thf('91', plain,
% 0.21/0.54      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (k1_tarski @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['71', '90'])).
% 0.21/0.54  thf('92', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))) | 
% 0.21/0.54       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('93', plain,
% 0.21/0.54      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.21/0.54         = (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.54  thf('94', plain,
% 0.21/0.54      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A))
% 0.21/0.54        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('95', plain,
% 0.21/0.54      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('split', [status(esa)], ['94'])).
% 0.21/0.54  thf('96', plain,
% 0.21/0.54      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup+', [status(thm)], ['93', '95'])).
% 0.21/0.54  thf('97', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf(d3_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ( v1_tex_2 @ B @ A ) <=>
% 0.21/0.54             ( ![C:$i]:
% 0.21/0.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.21/0.54                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('98', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X22 @ X23)
% 0.21/0.54          | ((sk_C_1 @ X22 @ X23) = (u1_struct_0 @ X22))
% 0.21/0.54          | (v1_tex_2 @ X22 @ X23)
% 0.21/0.54          | ~ (l1_pre_topc @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('99', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.54  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('101', plain,
% 0.21/0.54      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.21/0.54      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.54  thf('102', plain,
% 0.21/0.54      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('103', plain,
% 0.21/0.54      ((((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['101', '102'])).
% 0.21/0.54  thf('104', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X22 @ X23)
% 0.21/0.54          | ~ (v1_subset_1 @ (sk_C_1 @ X22 @ X23) @ (u1_struct_0 @ X23))
% 0.21/0.54          | (v1_tex_2 @ X22 @ X23)
% 0.21/0.54          | ~ (l1_pre_topc @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.21/0.54  thf('105', plain,
% 0.21/0.54      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54            (u1_struct_0 @ sk_A))
% 0.21/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['103', '104'])).
% 0.21/0.54  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('107', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('108', plain,
% 0.21/0.54      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54            (u1_struct_0 @ sk_A))
% 0.21/0.54         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.21/0.54  thf('109', plain,
% 0.21/0.54      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['3'])).
% 0.21/0.54  thf('110', plain,
% 0.21/0.54      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.21/0.54           (u1_struct_0 @ sk_A)))
% 0.21/0.54         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('clc', [status(thm)], ['108', '109'])).
% 0.21/0.54  thf('111', plain,
% 0.21/0.54      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.21/0.54       ~
% 0.21/0.54       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['96', '110'])).
% 0.21/0.54  thf('112', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['92', '111'])).
% 0.21/0.54  thf('113', plain,
% 0.21/0.54      (((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (k1_tarski @ sk_B_1))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['91', '112'])).
% 0.21/0.54  thf('114', plain,
% 0.21/0.54      ((((u1_struct_0 @ sk_A) = (k1_tarski @ sk_B_1)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf(t15_tex_2, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.21/0.54                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.21/0.54  thf('115', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X30 @ X31)
% 0.21/0.54          | ((u1_struct_0 @ X30) != (u1_struct_0 @ X31))
% 0.21/0.54          | ~ (v1_tex_2 @ X30 @ X31)
% 0.21/0.54          | ~ (l1_pre_topc @ X31))),
% 0.21/0.54      inference('cnf', [status(esa)], [t15_tex_2])).
% 0.21/0.54  thf('116', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (((u1_struct_0 @ X0) != (k1_tarski @ sk_B_1))
% 0.21/0.54           | ~ (l1_pre_topc @ sk_A)
% 0.21/0.54           | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.21/0.54           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['114', '115'])).
% 0.21/0.54  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('118', plain,
% 0.21/0.54      ((![X0 : $i]:
% 0.21/0.54          (((u1_struct_0 @ X0) != (k1_tarski @ sk_B_1))
% 0.21/0.54           | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.21/0.54           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 0.21/0.54         <= (~
% 0.21/0.54             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54               (u1_struct_0 @ sk_A))))),
% 0.21/0.54      inference('demod', [status(thm)], ['116', '117'])).
% 0.21/0.54  thf('119', plain,
% 0.21/0.54      (~
% 0.21/0.54       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['92', '111'])).
% 0.21/0.54  thf('120', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((u1_struct_0 @ X0) != (k1_tarski @ sk_B_1))
% 0.21/0.54          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.21/0.54          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['118', '119'])).
% 0.21/0.54  thf('121', plain,
% 0.21/0.54      ((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.21/0.54        | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.54        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['113', '120'])).
% 0.21/0.54  thf('122', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.54  thf('123', plain,
% 0.21/0.54      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.21/0.54         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['94'])).
% 0.21/0.54  thf('124', plain,
% 0.21/0.54      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.21/0.54       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.21/0.54         (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('split', [status(esa)], ['94'])).
% 0.21/0.54  thf('125', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['92', '111', '124'])).
% 0.21/0.54  thf('126', plain, ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['123', '125'])).
% 0.21/0.54  thf('127', plain, (((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['121', '122', '126'])).
% 0.21/0.54  thf('128', plain, ($false), inference('simplify', [status(thm)], ['127'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

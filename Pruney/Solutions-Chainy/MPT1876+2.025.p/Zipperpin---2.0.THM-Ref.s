%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.camUCaOiSN

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:59 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  197 (1087 expanded)
%              Number of leaves         :   41 ( 312 expanded)
%              Depth                    :   29
%              Number of atoms          : 1438 (13739 expanded)
%              Number of equality atoms :   22 ( 151 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t44_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tex_2])).

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( X28 = X27 )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X25 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t55_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_pre_topc])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( X25
        = ( u1_struct_0 @ ( sk_C @ X25 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('41',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','38','39','40'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','38','39','40'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X32 ) @ X31 ) @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['14','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X25 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('67',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('68',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','77'])).

thf('79',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('81',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ( X29
        = ( u1_struct_0 @ ( sk_C_1 @ X29 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('87',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('88',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','77','87'])).

thf('89',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['86','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['85','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('95',plain,(
    ! [X16: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ~ ( v7_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('96',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ( m1_pre_topc @ ( sk_C_1 @ X29 @ X30 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf(cc32_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('109',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ~ ( v1_tdlat_3 @ X23 )
      | ( v7_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_tdlat_3 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('115',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X29 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('117',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['110','111','112','113','125'])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v2_tex_2 @ X29 @ X30 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X29 @ X30 ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('137',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','77','87'])).

thf('143',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('145',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ X15 )
      | ( l1_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('146',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('149',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('150',plain,
    ( ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','77','87'])).

thf('152',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['150','151'])).

thf('153',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['96','143','152'])).

thf('154',plain,(
    $false ),
    inference(demod,[status(thm)],['79','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.camUCaOiSN
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 175 iterations in 0.123s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.58  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.38/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.58  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.38/0.58  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.38/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.38/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.38/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.58  thf(t44_tex_2, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.58           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.38/0.58            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.58              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.38/0.58  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf('3', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('4', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf(d1_xboole_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.58  thf('5', plain,
% 0.38/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.58  thf(t63_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.58       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X4 : $i, X5 : $i]:
% 0.38/0.58         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 0.38/0.58          | ~ (r2_hidden @ X4 @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X0)
% 0.38/0.58          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.58  thf(t3_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i]:
% 0.38/0.58         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.38/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf(t1_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.38/0.58           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.38/0.58  thf('10', plain,
% 0.38/0.58      (![X27 : $i, X28 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X27)
% 0.38/0.58          | ~ (v1_zfmisc_1 @ X27)
% 0.38/0.58          | ((X28) = (X27))
% 0.38/0.58          | ~ (r1_tarski @ X28 @ X27)
% 0.38/0.58          | (v1_xboole_0 @ X28))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.38/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.38/0.58          | ~ (v1_zfmisc_1 @ X0)
% 0.38/0.58          | (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_zfmisc_1 @ X0)
% 0.38/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.38/0.58          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.38/0.58          | (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['11'])).
% 0.38/0.58  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.38/0.58  thf('13', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X0)
% 0.38/0.58          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.38/0.58          | ~ (v1_zfmisc_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t10_tsep_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.58           ( ?[C:$i]:
% 0.38/0.58             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 0.38/0.58               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X25)
% 0.38/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.58          | (m1_pre_topc @ (sk_C @ X25 @ X26) @ X26)
% 0.38/0.58          | ~ (l1_pre_topc @ X26)
% 0.38/0.58          | (v2_struct_0 @ X26))),
% 0.38/0.58      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.38/0.58      inference('clc', [status(thm)], ['19', '20'])).
% 0.38/0.58  thf('22', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('23', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['21', '22'])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.58  thf(t1_subset, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.58  thf(t55_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.38/0.58           ( ![C:$i]:
% 0.38/0.58             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.38/0.58               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.58         ((v2_struct_0 @ X17)
% 0.38/0.58          | ~ (m1_pre_topc @ X17 @ X18)
% 0.38/0.58          | (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.38/0.58          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.38/0.58          | ~ (l1_pre_topc @ X18)
% 0.38/0.58          | (v2_struct_0 @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [t55_pre_topc])).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.38/0.58          | (v2_struct_0 @ X1)
% 0.38/0.58          | ~ (l1_pre_topc @ X1)
% 0.38/0.58          | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X1))
% 0.38/0.58          | ~ (m1_pre_topc @ X0 @ X1)
% 0.38/0.58          | (v2_struct_0 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (m1_subset_1 @ (sk_B @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))) @ 
% 0.38/0.58           (u1_struct_0 @ sk_A))
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['23', '28'])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X25)
% 0.38/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.58          | ((X25) = (u1_struct_0 @ (sk_C @ X25 @ X26)))
% 0.38/0.58          | ~ (l1_pre_topc @ X26)
% 0.38/0.58          | (v2_struct_0 @ X26))),
% 0.38/0.58      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.58  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.38/0.58      inference('clc', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('38', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('40', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '38', '39', '40'])).
% 0.38/0.58  thf(redefinition_k6_domain_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.58       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X20)
% 0.38/0.58          | ~ (m1_subset_1 @ X21 @ X20)
% 0.38/0.58          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.38/0.58      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.38/0.58            = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      (((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '38', '39', '40'])).
% 0.38/0.58  thf(t36_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (![X31 : $i, X32 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.38/0.58          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X32) @ X31) @ X32)
% 0.38/0.58          | ~ (l1_pre_topc @ X32)
% 0.38/0.58          | ~ (v2_pre_topc @ X32)
% 0.38/0.58          | (v2_struct_0 @ X32))),
% 0.38/0.58      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.38/0.58           sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.58  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.38/0.58           sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.38/0.58         sk_A)
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['43', '50'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.38/0.58      inference('simplify', [status(thm)], ['51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup+', [status(thm)], ['14', '52'])).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.38/0.58        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['4', '54'])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X25 : $i, X26 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X25)
% 0.38/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.38/0.58          | ~ (v2_struct_0 @ (sk_C @ X25 @ X26))
% 0.38/0.58          | ~ (l1_pre_topc @ X26)
% 0.38/0.58          | (v2_struct_0 @ X26))),
% 0.38/0.58      inference('cnf', [status(esa)], [t10_tsep_1])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('62', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('63', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('64', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('clc', [status(thm)], ['62', '63'])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A)
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58         | (v2_tex_2 @ sk_B_1 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['55', '64'])).
% 0.38/0.58  thf('66', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(cc1_subset_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X6 : $i, X7 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.38/0.58          | (v1_xboole_0 @ X6)
% 0.38/0.58          | ~ (v1_xboole_0 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['66', '67'])).
% 0.38/0.58  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('70', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('clc', [status(thm)], ['68', '69'])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['65', '70'])).
% 0.38/0.58  thf('72', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('73', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 0.38/0.58         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['71', '72'])).
% 0.38/0.58  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('75', plain,
% 0.38/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['73', '74'])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['0'])).
% 0.38/0.58  thf('77', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.38/0.58  thf('78', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['2', '77'])).
% 0.38/0.58  thf('79', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['1', '78'])).
% 0.38/0.58  thf('80', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t34_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.38/0.58             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.38/0.58           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.38/0.58                ( ![C:$i]:
% 0.38/0.58                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.38/0.58                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.38/0.58                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('81', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.38/0.58          | ~ (v2_tex_2 @ X29 @ X30)
% 0.38/0.58          | ((X29) = (u1_struct_0 @ (sk_C_1 @ X29 @ X30)))
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.58  thf('82', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['80', '81'])).
% 0.38/0.58  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('87', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('88', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['2', '77', '87'])).
% 0.38/0.58  thf('89', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['86', '88'])).
% 0.38/0.58  thf('90', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['85', '89'])).
% 0.38/0.58  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('92', plain,
% 0.38/0.58      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.58        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 0.38/0.58      inference('clc', [status(thm)], ['90', '91'])).
% 0.38/0.58  thf('93', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('94', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['92', '93'])).
% 0.38/0.58  thf(fc7_struct_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.58       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.38/0.58  thf('95', plain,
% 0.38/0.58      (![X16 : $i]:
% 0.38/0.58         ((v1_zfmisc_1 @ (u1_struct_0 @ X16))
% 0.38/0.58          | ~ (l1_struct_0 @ X16)
% 0.38/0.58          | ~ (v7_struct_0 @ X16))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.38/0.58  thf('96', plain,
% 0.38/0.58      (((v1_zfmisc_1 @ sk_B_1)
% 0.38/0.58        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['94', '95'])).
% 0.38/0.58  thf('97', plain,
% 0.38/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('98', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('99', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.38/0.58          | ~ (v2_tex_2 @ X29 @ X30)
% 0.38/0.58          | (m1_pre_topc @ (sk_C_1 @ X29 @ X30) @ X30)
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['98', '99'])).
% 0.38/0.58  thf('101', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('103', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.38/0.58         | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 0.38/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['97', '103'])).
% 0.38/0.58  thf('105', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('106', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['104', '105'])).
% 0.38/0.58  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('108', plain,
% 0.38/0.58      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['106', '107'])).
% 0.38/0.58  thf(cc32_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.38/0.58         ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.38/0.58             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('109', plain,
% 0.38/0.58      (![X23 : $i, X24 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X23 @ X24)
% 0.38/0.58          | ~ (v1_tdlat_3 @ X23)
% 0.38/0.58          | (v7_struct_0 @ X23)
% 0.38/0.58          | (v2_struct_0 @ X23)
% 0.38/0.58          | ~ (l1_pre_topc @ X24)
% 0.38/0.58          | ~ (v2_tdlat_3 @ X24)
% 0.38/0.58          | ~ (v2_pre_topc @ X24)
% 0.38/0.58          | (v2_struct_0 @ X24))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.38/0.58  thf('110', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A)
% 0.38/0.58         | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58         | ~ (v2_tdlat_3 @ sk_A)
% 0.38/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['108', '109'])).
% 0.38/0.58  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('112', plain, ((v2_tdlat_3 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('114', plain,
% 0.38/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('115', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('116', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.38/0.58          | ~ (v2_tex_2 @ X29 @ X30)
% 0.38/0.58          | (v1_tdlat_3 @ (sk_C_1 @ X29 @ X30))
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.58  thf('117', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['115', '116'])).
% 0.38/0.58  thf('118', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('119', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('120', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.38/0.58  thf('121', plain,
% 0.38/0.58      ((((v1_xboole_0 @ sk_B_1)
% 0.38/0.58         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['114', '120'])).
% 0.38/0.58  thf('122', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('123', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['121', '122'])).
% 0.38/0.58  thf('124', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('125', plain,
% 0.38/0.58      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['123', '124'])).
% 0.38/0.58  thf('126', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A)
% 0.38/0.58         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58         | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['110', '111', '112', '113', '125'])).
% 0.38/0.58  thf('127', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('128', plain,
% 0.38/0.58      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58         | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['126', '127'])).
% 0.38/0.58  thf('129', plain,
% 0.38/0.58      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('130', plain,
% 0.38/0.58      (![X29 : $i, X30 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X29)
% 0.38/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.38/0.58          | ~ (v2_tex_2 @ X29 @ X30)
% 0.38/0.58          | ~ (v2_struct_0 @ (sk_C_1 @ X29 @ X30))
% 0.38/0.58          | ~ (l1_pre_topc @ X30)
% 0.38/0.58          | ~ (v2_pre_topc @ X30)
% 0.38/0.58          | (v2_struct_0 @ X30))),
% 0.38/0.58      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.38/0.58  thf('131', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_pre_topc @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['129', '130'])).
% 0.38/0.58  thf('132', plain, ((v2_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('134', plain,
% 0.38/0.58      (((v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['131', '132', '133'])).
% 0.38/0.58  thf('135', plain,
% 0.38/0.58      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58         | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.38/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['128', '134'])).
% 0.38/0.58  thf('136', plain,
% 0.38/0.58      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['3'])).
% 0.38/0.58  thf('137', plain,
% 0.38/0.58      ((((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ sk_B_1)
% 0.38/0.58         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['135', '136'])).
% 0.38/0.58  thf('138', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('139', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['137', '138'])).
% 0.38/0.58  thf('140', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('141', plain,
% 0.38/0.58      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['139', '140'])).
% 0.38/0.58  thf('142', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['2', '77', '87'])).
% 0.38/0.58  thf('143', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['141', '142'])).
% 0.38/0.58  thf('144', plain,
% 0.38/0.58      (((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['106', '107'])).
% 0.38/0.58  thf(dt_m1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.58  thf('145', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X14 @ X15)
% 0.38/0.58          | (l1_pre_topc @ X14)
% 0.38/0.58          | ~ (l1_pre_topc @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.58  thf('146', plain,
% 0.38/0.58      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['144', '145'])).
% 0.38/0.58  thf('147', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('148', plain,
% 0.38/0.58      (((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['146', '147'])).
% 0.38/0.58  thf(dt_l1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.58  thf('149', plain,
% 0.38/0.58      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_pre_topc @ X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('150', plain,
% 0.38/0.58      (((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 0.38/0.58         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['148', '149'])).
% 0.38/0.58  thf('151', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['2', '77', '87'])).
% 0.38/0.58  thf('152', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['150', '151'])).
% 0.38/0.58  thf('153', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.38/0.58      inference('demod', [status(thm)], ['96', '143', '152'])).
% 0.38/0.58  thf('154', plain, ($false), inference('demod', [status(thm)], ['79', '153'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

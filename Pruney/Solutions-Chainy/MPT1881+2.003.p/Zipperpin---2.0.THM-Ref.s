%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ml99RAdeMQ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:12 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  309 (13803 expanded)
%              Number of leaves         :   40 (3964 expanded)
%              Depth                    :   39
%              Number of atoms          : 2657 (152028 expanded)
%              Number of equality atoms :   85 (3358 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t49_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tex_2 @ B @ A )
            <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( v1_subset_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('2',plain,
    ( ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B_3
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tex_2 @ X30 @ X31 )
      | ( m1_subset_1 @ ( sk_C @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v3_tex_2 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v2_tex_2 @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_tdlat_3 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('21',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
      | ( v3_tex_2 @ sk_B_3 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','20'])).

thf('22',plain,
    ( ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(rc3_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ? [B: $i] :
          ( ~ ( v1_subset_1 @ B @ A )
          & ~ ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X33 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_zfmisc_1 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[rc3_tex_2])).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X29 = X28 )
      | ( v1_subset_1 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( v1_subset_1 @ ( sk_B_2 @ X0 ) @ X0 )
      | ( ( sk_B_2 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X33: $i] :
      ( ~ ( v1_subset_1 @ ( sk_B_2 @ X33 ) @ X33 )
      | ( v1_zfmisc_1 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[rc3_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( sk_B_2 @ X0 )
        = X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B_2 @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ ( sk_B_2 @ X33 ) @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_zfmisc_1 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[rc3_tex_2])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( r1_tarski @ ( sk_B_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('34',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( m1_subset_1 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k1_tarski @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X7: $i] :
      ( v1_xboole_0 @ ( sk_B @ X7 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('49',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','53'])).

thf('55',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v2_tex_2 @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_tdlat_3 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('60',plain,
    ( ( v3_tex_2 @ sk_B_3 @ sk_A )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_tex_2 @ X30 @ X31 )
      | ~ ( v2_tex_2 @ X32 @ X31 )
      | ~ ( r1_tarski @ X30 @ X32 )
      | ( X30 = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_3 = X0 )
      | ~ ( r1_tarski @ sk_B_3 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( sk_B_3 = X0 )
      | ~ ( r1_tarski @ sk_B_3 @ X0 )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( r1_tarski @ sk_B_3 @ X0 )
        | ( sk_B_3 = X0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    r1_tarski @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_tdlat_3 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( ( sk_B_3
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('81',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( v1_xboole_0 @ sk_B_3 )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('86',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','86'])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('89',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','86'])).

thf('90',plain,
    ( ( ~ ( v1_zfmisc_1 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ~ ( v1_zfmisc_1 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( sk_B_3
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['77','87'])).

thf('93',plain,
    ( ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['78'])).

thf('94',plain,
    ( ( ( v1_subset_1 @ sk_B_3 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B_2 @ X0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('96',plain,(
    ! [X33: $i] :
      ( ~ ( v1_subset_1 @ ( sk_B_2 @ X33 ) @ X33 )
      | ( v1_zfmisc_1 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[rc3_tex_2])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_subset_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_zfmisc_1 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','98'])).

thf('100',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('102',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_zfmisc_1 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v1_zfmisc_1 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_3 )
      | ( v1_xboole_0 @ sk_B_3 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( v3_tex_2 @ sk_B_3 @ sk_A )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('107',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf('108',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_tex_2 @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v1_xboole_0 @ sk_B_3 )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_zfmisc_1 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['105','115'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_zfmisc_1 @ sk_B_3 )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_B_3 )
      | ( ( u1_struct_0 @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ sk_B_3 )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('123',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('125',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B_3 ) )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
   <= ( ( v3_tex_2 @ sk_B_3 @ sk_A )
      & ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_xboole_0 @ sk_B_3 )
   <= ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('129',plain,
    ( ~ ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('131',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
    | ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['21','130'])).

thf('132',plain,
    ( ~ ( v3_tex_2 @ sk_B_3 @ sk_A )
   <= ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['78'])).

thf('133',plain,
    ( ~ ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['78'])).

thf('134',plain,(
    ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['22','129','133'])).

thf('135',plain,(
    ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['132','134'])).

thf('136',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) ),
    inference(clc,[status(thm)],['131','135'])).

thf('137',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('138',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf(t8_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('140',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( X13 = X11 )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X13 @ X12 ) @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('141',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( m1_subset_1 @ ( sk_D @ sk_B_3 @ X0 @ sk_B_3 ) @ sk_B_3 )
        | ( X0 = sk_B_3 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B_3 @ X0 @ sk_B_3 ) @ sk_B_3 )
      | ( X0 = sk_B_3 ) ) ),
    inference(simpl_trail,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( sk_C @ sk_B_3 @ sk_A )
      = sk_B_3 )
    | ( m1_subset_1 @ ( sk_D @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,
    ( ( m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('146',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('147',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('149',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tex_2 @ X30 @ X31 )
      | ( X30
       != ( sk_C @ X30 @ X31 ) )
      | ( v3_tex_2 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('150',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( X0
         != ( sk_C @ X0 @ sk_A ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( X0
         != ( sk_C @ X0 @ sk_A ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
      | ( v3_tex_2 @ X0 @ sk_A )
      | ( X0
       != ( sk_C @ X0 @ sk_A ) )
      | ~ ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( v2_tex_2 @ sk_B_3 @ sk_A )
    | ( sk_B_3
     != ( sk_C @ sk_B_3 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['147','154'])).

thf('156',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('157',plain,
    ( ( sk_B_3
     != ( sk_C @ sk_B_3 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['132','134'])).

thf('159',plain,(
    sk_B_3
 != ( sk_C @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ ( sk_D @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) @ sk_B_3 ),
    inference('simplify_reflect-',[status(thm)],['144','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('162',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( r2_hidden @ ( sk_D @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('164',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('165',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v2_tex_2 @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_tdlat_3 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('166',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( v1_tdlat_3 @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167','168','169'])).

thf('171',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','172'])).

thf('174',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('175',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tex_2 @ X30 @ X31 )
      | ( m1_subset_1 @ ( sk_C @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v3_tex_2 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('179',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
      | ( v3_tex_2 @ k1_xboole_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178','179'])).

thf('181',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('182',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('183',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v3_tex_2 @ X36 @ X37 )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t46_tex_2])).

thf('184',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v3_tex_2 @ X0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v3_tex_2 @ X0 @ sk_A )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','187'])).

thf('189',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('190',plain,
    ( ( ~ ( v3_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ~ ( v3_tex_2 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['180','192'])).

thf('194',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('195',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( X13 = X11 )
      | ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X13 )
      | ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ( ( sk_C @ k1_xboole_0 @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B_3 ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B_3 ) @ k1_xboole_0 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('199',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( X0
         != ( sk_C @ X0 @ sk_A ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('200',plain,
    ( ( ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ sk_A ) )
      | ( v3_tex_2 @ k1_xboole_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['163','172'])).

thf('202',plain,
    ( ( ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ sk_A ) )
      | ( v3_tex_2 @ k1_xboole_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( v3_tex_2 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('204',plain,
    ( ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B_3 ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B_3 ) @ k1_xboole_0 ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['197','204'])).

thf('206',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('207',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B_3 ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B_3 ) @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('209',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('210',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_tarski @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('212',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['210','215'])).

thf('217',plain,(
    r2_hidden @ ( sk_D @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_B_3 ) @ ( sk_C @ k1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['207','216'])).

thf('218',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('219',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ( v2_tex_2 @ X34 @ X35 )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v1_tdlat_3 @ X35 )
      | ~ ( v2_pre_topc @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_tex_2 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['217','225'])).

thf('227',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('228',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('229',plain,
    ( sk_B_3
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['227','228'])).

thf('230',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ~ ( v1_xboole_0 @ sk_B_3 )
    | ( v3_tex_2 @ k1_xboole_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['226','229','230','231','232'])).

thf('234',plain,
    ( ~ ( v3_tex_2 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['190','191'])).

thf('235',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('236',plain,(
    ~ ( v3_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['234','235'])).

thf('237',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(clc,[status(thm)],['233','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    r2_hidden @ ( sk_D @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) @ sk_B_3 ),
    inference(clc,[status(thm)],['162','239'])).

thf('241',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['145','146'])).

thf('242',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( X13 = X11 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X13 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t8_subset_1])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_3 @ X0 @ sk_B_3 ) @ sk_B_3 )
      | ~ ( r2_hidden @ ( sk_D @ sk_B_3 @ X0 @ sk_B_3 ) @ X0 )
      | ( X0 = sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ( ( sk_C @ sk_B_3 @ sk_A )
      = sk_B_3 )
    | ~ ( r2_hidden @ ( sk_D @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) @ ( sk_C @ sk_B_3 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['240','243'])).

thf('245',plain,(
    r2_hidden @ ( sk_D @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) @ sk_B_3 ),
    inference(clc,[status(thm)],['162','239'])).

thf('246',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['145','146'])).

thf('247',plain,
    ( ( sk_B_3
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('248',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_tex_2 @ X30 @ X31 )
      | ( r1_tarski @ X30 @ ( sk_C @ X30 @ X31 ) )
      | ( v3_tex_2 @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('249',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( r1_tarski @ X0 @ ( sk_C @ X0 @ sk_A ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v3_tex_2 @ X0 @ sk_A )
        | ( r1_tarski @ X0 @ ( sk_C @ X0 @ sk_A ) )
        | ~ ( v2_tex_2 @ X0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['22','129'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
      | ( v3_tex_2 @ X0 @ sk_A )
      | ( r1_tarski @ X0 @ ( sk_C @ X0 @ sk_A ) )
      | ~ ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['251','252'])).

thf('254',plain,
    ( ~ ( v2_tex_2 @ sk_B_3 @ sk_A )
    | ( r1_tarski @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['246','253'])).

thf('255',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(clc,[status(thm)],['17','18'])).

thf('256',plain,
    ( ( r1_tarski @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) )
    | ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['132','134'])).

thf('258',plain,(
    r1_tarski @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['256','257'])).

thf('259',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('260',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('261',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_C @ sk_B_3 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    r2_hidden @ ( sk_D @ sk_B_3 @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) @ ( sk_C @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['245','262'])).

thf('264',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) ),
    inference(clc,[status(thm)],['131','135'])).

thf('265',plain,
    ( ( sk_C @ sk_B_3 @ sk_A )
    = sk_B_3 ),
    inference(demod,[status(thm)],['244','263','264'])).

thf('266',plain,(
    sk_B_3
 != ( sk_C @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('267',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['265','266'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ml99RAdeMQ
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.53/1.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.71  % Solved by: fo/fo7.sh
% 1.53/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.71  % done 2150 iterations in 1.246s
% 1.53/1.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.71  % SZS output start Refutation
% 1.53/1.71  thf(sk_B_type, type, sk_B: $i > $i).
% 1.53/1.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.53/1.71  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 1.53/1.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.53/1.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.53/1.71  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 1.53/1.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.53/1.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.53/1.71  thf(sk_B_3_type, type, sk_B_3: $i).
% 1.53/1.71  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.53/1.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.53/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.53/1.71  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.53/1.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.53/1.71  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.53/1.71  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.53/1.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.53/1.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.53/1.71  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.53/1.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.53/1.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.53/1.71  thf(t49_tex_2, conjecture,
% 1.53/1.71    (![A:$i]:
% 1.53/1.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 1.53/1.71         ( l1_pre_topc @ A ) ) =>
% 1.53/1.71       ( ![B:$i]:
% 1.53/1.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.71           ( ( v3_tex_2 @ B @ A ) <=>
% 1.53/1.71             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.53/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.71    (~( ![A:$i]:
% 1.53/1.71        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.53/1.71            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.71          ( ![B:$i]:
% 1.53/1.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.71              ( ( v3_tex_2 @ B @ A ) <=>
% 1.53/1.71                ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 1.53/1.71    inference('cnf.neg', [status(esa)], [t49_tex_2])).
% 1.53/1.71  thf('0', plain,
% 1.53/1.71      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf(d7_subset_1, axiom,
% 1.53/1.71    (![A:$i,B:$i]:
% 1.53/1.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.71       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 1.53/1.71  thf('1', plain,
% 1.53/1.71      (![X28 : $i, X29 : $i]:
% 1.53/1.71         (((X29) = (X28))
% 1.53/1.71          | (v1_subset_1 @ X29 @ X28)
% 1.53/1.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 1.53/1.71      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.53/1.71  thf('2', plain,
% 1.53/1.71      (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 1.53/1.71        | ((sk_B_3) = (u1_struct_0 @ sk_A)))),
% 1.53/1.71      inference('sup-', [status(thm)], ['0', '1'])).
% 1.53/1.71  thf('3', plain,
% 1.53/1.71      ((~ (v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 1.53/1.71        | (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf('4', plain,
% 1.53/1.71      ((~ (v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))
% 1.53/1.71         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.71      inference('split', [status(esa)], ['3'])).
% 1.53/1.71  thf('5', plain,
% 1.53/1.71      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.71         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.71      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.71  thf('6', plain,
% 1.53/1.71      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf(d7_tex_2, axiom,
% 1.53/1.71    (![A:$i]:
% 1.53/1.71     ( ( l1_pre_topc @ A ) =>
% 1.53/1.71       ( ![B:$i]:
% 1.53/1.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.71           ( ( v3_tex_2 @ B @ A ) <=>
% 1.53/1.71             ( ( v2_tex_2 @ B @ A ) & 
% 1.53/1.71               ( ![C:$i]:
% 1.53/1.71                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.71                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.53/1.71                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.53/1.71  thf('7', plain,
% 1.53/1.71      (![X30 : $i, X31 : $i]:
% 1.53/1.71         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.71          | ~ (v2_tex_2 @ X30 @ X31)
% 1.53/1.71          | (m1_subset_1 @ (sk_C @ X30 @ X31) @ 
% 1.53/1.71             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.71          | (v3_tex_2 @ X30 @ X31)
% 1.53/1.71          | ~ (l1_pre_topc @ X31))),
% 1.53/1.71      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.53/1.71  thf('8', plain,
% 1.53/1.71      ((~ (l1_pre_topc @ sk_A)
% 1.53/1.71        | (v3_tex_2 @ sk_B_3 @ sk_A)
% 1.53/1.71        | (m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ 
% 1.53/1.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.71        | ~ (v2_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.71      inference('sup-', [status(thm)], ['6', '7'])).
% 1.53/1.71  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf('10', plain,
% 1.53/1.71      (((v3_tex_2 @ sk_B_3 @ sk_A)
% 1.53/1.71        | (m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ 
% 1.53/1.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.71        | ~ (v2_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.71      inference('demod', [status(thm)], ['8', '9'])).
% 1.53/1.71  thf('11', plain,
% 1.53/1.71      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf(t43_tex_2, axiom,
% 1.53/1.71    (![A:$i]:
% 1.53/1.71     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 1.53/1.71         ( l1_pre_topc @ A ) ) =>
% 1.53/1.71       ( ![B:$i]:
% 1.53/1.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.71           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.53/1.71  thf('12', plain,
% 1.53/1.71      (![X34 : $i, X35 : $i]:
% 1.53/1.71         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.53/1.71          | (v2_tex_2 @ X34 @ X35)
% 1.53/1.71          | ~ (l1_pre_topc @ X35)
% 1.53/1.71          | ~ (v1_tdlat_3 @ X35)
% 1.53/1.71          | ~ (v2_pre_topc @ X35)
% 1.53/1.71          | (v2_struct_0 @ X35))),
% 1.53/1.71      inference('cnf', [status(esa)], [t43_tex_2])).
% 1.53/1.71  thf('13', plain,
% 1.53/1.71      (((v2_struct_0 @ sk_A)
% 1.53/1.71        | ~ (v2_pre_topc @ sk_A)
% 1.53/1.71        | ~ (v1_tdlat_3 @ sk_A)
% 1.53/1.71        | ~ (l1_pre_topc @ sk_A)
% 1.53/1.71        | (v2_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.71      inference('sup-', [status(thm)], ['11', '12'])).
% 1.53/1.71  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf('15', plain, ((v1_tdlat_3 @ sk_A)),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf('17', plain, (((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.71      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 1.53/1.71  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.71  thf('19', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.53/1.71      inference('clc', [status(thm)], ['17', '18'])).
% 1.53/1.71  thf('20', plain,
% 1.53/1.71      (((v3_tex_2 @ sk_B_3 @ sk_A)
% 1.53/1.71        | (m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ 
% 1.53/1.71           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.71      inference('demod', [status(thm)], ['10', '19'])).
% 1.53/1.71  thf('21', plain,
% 1.53/1.71      ((((m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.71         | (v3_tex_2 @ sk_B_3 @ sk_A)))
% 1.53/1.71         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.71      inference('sup+', [status(thm)], ['5', '20'])).
% 1.53/1.71  thf('22', plain,
% 1.53/1.71      (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))) | 
% 1.53/1.71       ((v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.71      inference('split', [status(esa)], ['3'])).
% 1.53/1.71  thf(rc3_tex_2, axiom,
% 1.53/1.71    (![A:$i]:
% 1.53/1.71     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 1.53/1.71       ( ?[B:$i]:
% 1.53/1.71         ( ( ~( v1_subset_1 @ B @ A ) ) & ( ~( v1_zfmisc_1 @ B ) ) & 
% 1.53/1.71           ( ~( v1_xboole_0 @ B ) ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ))).
% 1.53/1.71  thf('23', plain,
% 1.53/1.71      (![X33 : $i]:
% 1.53/1.71         ((m1_subset_1 @ (sk_B_2 @ X33) @ (k1_zfmisc_1 @ X33))
% 1.53/1.71          | (v1_zfmisc_1 @ X33)
% 1.53/1.71          | (v1_xboole_0 @ X33))),
% 1.53/1.71      inference('cnf', [status(esa)], [rc3_tex_2])).
% 1.53/1.71  thf('24', plain,
% 1.53/1.71      (![X28 : $i, X29 : $i]:
% 1.53/1.71         (((X29) = (X28))
% 1.53/1.71          | (v1_subset_1 @ X29 @ X28)
% 1.53/1.71          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 1.53/1.71      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.53/1.71  thf('25', plain,
% 1.53/1.71      (![X0 : $i]:
% 1.53/1.71         ((v1_xboole_0 @ X0)
% 1.53/1.71          | (v1_zfmisc_1 @ X0)
% 1.53/1.71          | (v1_subset_1 @ (sk_B_2 @ X0) @ X0)
% 1.53/1.71          | ((sk_B_2 @ X0) = (X0)))),
% 1.53/1.71      inference('sup-', [status(thm)], ['23', '24'])).
% 1.53/1.71  thf('26', plain,
% 1.53/1.71      (![X33 : $i]:
% 1.53/1.71         (~ (v1_subset_1 @ (sk_B_2 @ X33) @ X33)
% 1.53/1.71          | (v1_zfmisc_1 @ X33)
% 1.53/1.71          | (v1_xboole_0 @ X33))),
% 1.53/1.71      inference('cnf', [status(esa)], [rc3_tex_2])).
% 1.53/1.71  thf('27', plain,
% 1.53/1.71      (![X0 : $i]:
% 1.53/1.71         (((sk_B_2 @ X0) = (X0))
% 1.53/1.72          | (v1_zfmisc_1 @ X0)
% 1.53/1.72          | (v1_xboole_0 @ X0)
% 1.53/1.72          | (v1_xboole_0 @ X0)
% 1.53/1.72          | (v1_zfmisc_1 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['25', '26'])).
% 1.53/1.72  thf('28', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v1_xboole_0 @ X0) | (v1_zfmisc_1 @ X0) | ((sk_B_2 @ X0) = (X0)))),
% 1.53/1.72      inference('simplify', [status(thm)], ['27'])).
% 1.53/1.72  thf('29', plain,
% 1.53/1.72      (![X33 : $i]:
% 1.53/1.72         ((m1_subset_1 @ (sk_B_2 @ X33) @ (k1_zfmisc_1 @ X33))
% 1.53/1.72          | (v1_zfmisc_1 @ X33)
% 1.53/1.72          | (v1_xboole_0 @ X33))),
% 1.53/1.72      inference('cnf', [status(esa)], [rc3_tex_2])).
% 1.53/1.72  thf(t3_subset, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.53/1.72  thf('30', plain,
% 1.53/1.72      (![X16 : $i, X17 : $i]:
% 1.53/1.72         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.72  thf('31', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v1_xboole_0 @ X0)
% 1.53/1.72          | (v1_zfmisc_1 @ X0)
% 1.53/1.72          | (r1_tarski @ (sk_B_2 @ X0) @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['29', '30'])).
% 1.53/1.72  thf('32', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((r1_tarski @ X0 @ X0)
% 1.53/1.72          | (v1_zfmisc_1 @ X0)
% 1.53/1.72          | (v1_xboole_0 @ X0)
% 1.53/1.72          | (v1_zfmisc_1 @ X0)
% 1.53/1.72          | (v1_xboole_0 @ X0))),
% 1.53/1.72      inference('sup+', [status(thm)], ['28', '31'])).
% 1.53/1.72  thf('33', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v1_xboole_0 @ X0) | (v1_zfmisc_1 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.53/1.72      inference('simplify', [status(thm)], ['32'])).
% 1.53/1.72  thf(t1_zfmisc_1, axiom,
% 1.53/1.72    (( k1_zfmisc_1 @ k1_xboole_0 ) = ( k1_tarski @ k1_xboole_0 ))).
% 1.53/1.72  thf('34', plain, (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 1.53/1.72      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 1.53/1.72  thf(t4_subset_1, axiom,
% 1.53/1.72    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.53/1.72  thf('35', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf(d2_subset_1, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( ( v1_xboole_0 @ A ) =>
% 1.53/1.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.53/1.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.53/1.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.53/1.72  thf('36', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ X1)
% 1.53/1.72          | (r2_hidden @ X0 @ X1)
% 1.53/1.72          | (v1_xboole_0 @ X1))),
% 1.53/1.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.53/1.72  thf('37', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.53/1.72          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['35', '36'])).
% 1.53/1.72  thf(fc1_subset_1, axiom,
% 1.53/1.72    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.53/1.72  thf('38', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 1.53/1.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.53/1.72  thf('39', plain,
% 1.53/1.72      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.53/1.72      inference('clc', [status(thm)], ['37', '38'])).
% 1.53/1.72  thf('40', plain, ((r2_hidden @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 1.53/1.72      inference('sup+', [status(thm)], ['34', '39'])).
% 1.53/1.72  thf('41', plain,
% 1.53/1.72      (![X1 : $i, X2 : $i]:
% 1.53/1.72         (~ (v1_xboole_0 @ X2) | (m1_subset_1 @ X2 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.53/1.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.53/1.72  thf(t55_subset_1, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( m1_subset_1 @ B @ A ) =>
% 1.53/1.72       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 1.53/1.72         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.53/1.72  thf('42', plain,
% 1.53/1.72      (![X9 : $i, X10 : $i]:
% 1.53/1.72         (((X9) = (k1_xboole_0))
% 1.53/1.72          | ~ (m1_subset_1 @ X10 @ X9)
% 1.53/1.72          | (m1_subset_1 @ (k1_tarski @ X10) @ (k1_zfmisc_1 @ X9)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t55_subset_1])).
% 1.53/1.72  thf('43', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         (~ (v1_xboole_0 @ X0)
% 1.53/1.72          | ~ (v1_xboole_0 @ X1)
% 1.53/1.72          | (m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X0))
% 1.53/1.72          | ((X0) = (k1_xboole_0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['41', '42'])).
% 1.53/1.72  thf(t5_subset, axiom,
% 1.53/1.72    (![A:$i,B:$i,C:$i]:
% 1.53/1.72     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.53/1.72          ( v1_xboole_0 @ C ) ) ))).
% 1.53/1.72  thf('44', plain,
% 1.53/1.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.53/1.72         (~ (r2_hidden @ X22 @ X23)
% 1.53/1.72          | ~ (v1_xboole_0 @ X24)
% 1.53/1.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t5_subset])).
% 1.53/1.72  thf('45', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.72         (((X0) = (k1_xboole_0))
% 1.53/1.72          | ~ (v1_xboole_0 @ X1)
% 1.53/1.72          | ~ (v1_xboole_0 @ X0)
% 1.53/1.72          | ~ (v1_xboole_0 @ X0)
% 1.53/1.72          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['43', '44'])).
% 1.53/1.72  thf('46', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.72         (~ (r2_hidden @ X2 @ (k1_tarski @ X1))
% 1.53/1.72          | ~ (v1_xboole_0 @ X0)
% 1.53/1.72          | ~ (v1_xboole_0 @ X1)
% 1.53/1.72          | ((X0) = (k1_xboole_0)))),
% 1.53/1.72      inference('simplify', [status(thm)], ['45'])).
% 1.53/1.72  thf('47', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (((X0) = (k1_xboole_0))
% 1.53/1.72          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.53/1.72          | ~ (v1_xboole_0 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['40', '46'])).
% 1.53/1.72  thf(rc2_subset_1, axiom,
% 1.53/1.72    (![A:$i]:
% 1.53/1.72     ( ?[B:$i]:
% 1.53/1.72       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 1.53/1.72  thf('48', plain, (![X7 : $i]: (v1_xboole_0 @ (sk_B @ X7))),
% 1.53/1.72      inference('cnf', [status(esa)], [rc2_subset_1])).
% 1.53/1.72  thf('49', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf(cc1_subset_1, axiom,
% 1.53/1.72    (![A:$i]:
% 1.53/1.72     ( ( v1_xboole_0 @ A ) =>
% 1.53/1.72       ( ![B:$i]:
% 1.53/1.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 1.53/1.72  thf('50', plain,
% 1.53/1.72      (![X14 : $i, X15 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.53/1.72          | (v1_xboole_0 @ X14)
% 1.53/1.72          | ~ (v1_xboole_0 @ X15))),
% 1.53/1.72      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.53/1.72  thf('51', plain,
% 1.53/1.72      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['49', '50'])).
% 1.53/1.72  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.53/1.72      inference('sup-', [status(thm)], ['48', '51'])).
% 1.53/1.72  thf('53', plain,
% 1.53/1.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.53/1.72      inference('demod', [status(thm)], ['47', '52'])).
% 1.53/1.72  thf('54', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((r1_tarski @ X0 @ X0) | (v1_zfmisc_1 @ X0) | ((X0) = (k1_xboole_0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['33', '53'])).
% 1.53/1.72  thf('55', plain,
% 1.53/1.72      (![X16 : $i, X18 : $i]:
% 1.53/1.72         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 1.53/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.72  thf('56', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (((X0) = (k1_xboole_0))
% 1.53/1.72          | (v1_zfmisc_1 @ X0)
% 1.53/1.72          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['54', '55'])).
% 1.53/1.72  thf('57', plain,
% 1.53/1.72      (![X34 : $i, X35 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.53/1.72          | (v2_tex_2 @ X34 @ X35)
% 1.53/1.72          | ~ (l1_pre_topc @ X35)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X35)
% 1.53/1.72          | ~ (v2_pre_topc @ X35)
% 1.53/1.72          | (v2_struct_0 @ X35))),
% 1.53/1.72      inference('cnf', [status(esa)], [t43_tex_2])).
% 1.53/1.72  thf('58', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 1.53/1.72          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ~ (v2_pre_topc @ X0)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X0)
% 1.53/1.72          | ~ (l1_pre_topc @ X0)
% 1.53/1.72          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['56', '57'])).
% 1.53/1.72  thf('59', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (((X0) = (k1_xboole_0))
% 1.53/1.72          | (v1_zfmisc_1 @ X0)
% 1.53/1.72          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['54', '55'])).
% 1.53/1.72  thf('60', plain,
% 1.53/1.72      (((v3_tex_2 @ sk_B_3 @ sk_A)) <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('split', [status(esa)], ['3'])).
% 1.53/1.72  thf('61', plain,
% 1.53/1.72      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('62', plain,
% 1.53/1.72      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.72          | ~ (v3_tex_2 @ X30 @ X31)
% 1.53/1.72          | ~ (v2_tex_2 @ X32 @ X31)
% 1.53/1.72          | ~ (r1_tarski @ X30 @ X32)
% 1.53/1.72          | ((X30) = (X32))
% 1.53/1.72          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.72          | ~ (l1_pre_topc @ X31))),
% 1.53/1.72      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.53/1.72  thf('63', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_pre_topc @ sk_A)
% 1.53/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.72          | ((sk_B_3) = (X0))
% 1.53/1.72          | ~ (r1_tarski @ sk_B_3 @ X0)
% 1.53/1.72          | ~ (v2_tex_2 @ X0 @ sk_A)
% 1.53/1.72          | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('sup-', [status(thm)], ['61', '62'])).
% 1.53/1.72  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('65', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.72          | ((sk_B_3) = (X0))
% 1.53/1.72          | ~ (r1_tarski @ sk_B_3 @ X0)
% 1.53/1.72          | ~ (v2_tex_2 @ X0 @ sk_A)
% 1.53/1.72          | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('demod', [status(thm)], ['63', '64'])).
% 1.53/1.72  thf('66', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (v2_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | ~ (r1_tarski @ sk_B_3 @ X0)
% 1.53/1.72           | ((sk_B_3) = (X0))
% 1.53/1.72           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['60', '65'])).
% 1.53/1.72  thf('67', plain,
% 1.53/1.72      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | ((sk_B_3) = (u1_struct_0 @ sk_A))
% 1.53/1.72         | ~ (r1_tarski @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 1.53/1.72         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['59', '66'])).
% 1.53/1.72  thf('68', plain,
% 1.53/1.72      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('69', plain,
% 1.53/1.72      (![X16 : $i, X17 : $i]:
% 1.53/1.72         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.72  thf('70', plain, ((r1_tarski @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 1.53/1.72      inference('sup-', [status(thm)], ['68', '69'])).
% 1.53/1.72  thf('71', plain,
% 1.53/1.72      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | ((sk_B_3) = (u1_struct_0 @ sk_A))
% 1.53/1.72         | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('demod', [status(thm)], ['67', '70'])).
% 1.53/1.72  thf('72', plain,
% 1.53/1.72      (((~ (l1_pre_topc @ sk_A)
% 1.53/1.72         | ~ (v1_tdlat_3 @ sk_A)
% 1.53/1.72         | ~ (v2_pre_topc @ sk_A)
% 1.53/1.72         | (v2_struct_0 @ sk_A)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.53/1.72         | ((sk_B_3) = (u1_struct_0 @ sk_A))
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['58', '71'])).
% 1.53/1.72  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('74', plain, ((v1_tdlat_3 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('76', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.53/1.72         | ((sk_B_3) = (u1_struct_0 @ sk_A))
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 1.53/1.72  thf('77', plain,
% 1.53/1.72      (((((sk_B_3) = (u1_struct_0 @ sk_A))
% 1.53/1.72         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v2_struct_0 @ sk_A))) <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('simplify', [status(thm)], ['76'])).
% 1.53/1.72  thf('78', plain,
% 1.53/1.72      (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 1.53/1.72        | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('79', plain,
% 1.53/1.72      (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('split', [status(esa)], ['78'])).
% 1.53/1.72  thf('80', plain,
% 1.53/1.72      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf(cc2_tex_2, axiom,
% 1.53/1.72    (![A:$i]:
% 1.53/1.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.53/1.72       ( ![B:$i]:
% 1.53/1.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.72           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 1.53/1.72  thf('81', plain,
% 1.53/1.72      (![X26 : $i, X27 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 1.53/1.72          | ~ (v1_subset_1 @ X26 @ X27)
% 1.53/1.72          | (v1_xboole_0 @ X26)
% 1.53/1.72          | ~ (v1_zfmisc_1 @ X27)
% 1.53/1.72          | (v1_xboole_0 @ X27))),
% 1.53/1.72      inference('cnf', [status(esa)], [cc2_tex_2])).
% 1.53/1.72  thf('82', plain,
% 1.53/1.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.53/1.72        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.53/1.72        | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72        | ~ (v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['80', '81'])).
% 1.53/1.72  thf('83', plain,
% 1.53/1.72      ((((v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.53/1.72         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 1.53/1.72         <= (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['79', '82'])).
% 1.53/1.72  thf('84', plain,
% 1.53/1.72      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('85', plain,
% 1.53/1.72      (![X14 : $i, X15 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.53/1.72          | (v1_xboole_0 @ X14)
% 1.53/1.72          | ~ (v1_xboole_0 @ X15))),
% 1.53/1.72      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.53/1.72  thf('86', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_3))),
% 1.53/1.72      inference('sup-', [status(thm)], ['84', '85'])).
% 1.53/1.72  thf('87', plain,
% 1.53/1.72      (((~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['83', '86'])).
% 1.53/1.72  thf('88', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | ((sk_B_3) = (u1_struct_0 @ sk_A))
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['77', '87'])).
% 1.53/1.72  thf('89', plain,
% 1.53/1.72      (((~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['83', '86'])).
% 1.53/1.72  thf('90', plain,
% 1.53/1.72      (((~ (v1_zfmisc_1 @ sk_B_3)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v2_struct_0 @ sk_A)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['88', '89'])).
% 1.53/1.72  thf('91', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | ~ (v1_zfmisc_1 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('simplify', [status(thm)], ['90'])).
% 1.53/1.72  thf('92', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | ((sk_B_3) = (u1_struct_0 @ sk_A))
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['77', '87'])).
% 1.53/1.72  thf('93', plain,
% 1.53/1.72      (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('split', [status(esa)], ['78'])).
% 1.53/1.72  thf('94', plain,
% 1.53/1.72      ((((v1_subset_1 @ sk_B_3 @ sk_B_3)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v2_struct_0 @ sk_A)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup+', [status(thm)], ['92', '93'])).
% 1.53/1.72  thf('95', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v1_xboole_0 @ X0) | (v1_zfmisc_1 @ X0) | ((sk_B_2 @ X0) = (X0)))),
% 1.53/1.72      inference('simplify', [status(thm)], ['27'])).
% 1.53/1.72  thf('96', plain,
% 1.53/1.72      (![X33 : $i]:
% 1.53/1.72         (~ (v1_subset_1 @ (sk_B_2 @ X33) @ X33)
% 1.53/1.72          | (v1_zfmisc_1 @ X33)
% 1.53/1.72          | (v1_xboole_0 @ X33))),
% 1.53/1.72      inference('cnf', [status(esa)], [rc3_tex_2])).
% 1.53/1.72  thf('97', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (v1_subset_1 @ X0 @ X0)
% 1.53/1.72          | (v1_zfmisc_1 @ X0)
% 1.53/1.72          | (v1_xboole_0 @ X0)
% 1.53/1.72          | (v1_xboole_0 @ X0)
% 1.53/1.72          | (v1_zfmisc_1 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['95', '96'])).
% 1.53/1.72  thf('98', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v1_xboole_0 @ X0) | (v1_zfmisc_1 @ X0) | ~ (v1_subset_1 @ X0 @ X0))),
% 1.53/1.72      inference('simplify', [status(thm)], ['97'])).
% 1.53/1.72  thf('99', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | (v1_zfmisc_1 @ sk_B_3)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['94', '98'])).
% 1.53/1.72  thf('100', plain,
% 1.53/1.72      ((((v1_zfmisc_1 @ sk_B_3)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v2_struct_0 @ sk_A)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('simplify', [status(thm)], ['99'])).
% 1.53/1.72  thf('101', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_3))),
% 1.53/1.72      inference('sup-', [status(thm)], ['84', '85'])).
% 1.53/1.72  thf('102', plain,
% 1.53/1.72      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.53/1.72         | (v2_struct_0 @ sk_A)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | (v1_zfmisc_1 @ sk_B_3)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['100', '101'])).
% 1.53/1.72  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.53/1.72      inference('sup-', [status(thm)], ['48', '51'])).
% 1.53/1.72  thf('104', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)
% 1.53/1.72         | (v1_zfmisc_1 @ sk_B_3)
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['102', '103'])).
% 1.53/1.72  thf('105', plain,
% 1.53/1.72      ((((v1_zfmisc_1 @ sk_B_3) | (v1_xboole_0 @ sk_B_3) | (v2_struct_0 @ sk_A)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('simplify', [status(thm)], ['104'])).
% 1.53/1.72  thf('106', plain,
% 1.53/1.72      (((v3_tex_2 @ sk_B_3 @ sk_A)) <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('split', [status(esa)], ['3'])).
% 1.53/1.72  thf('107', plain,
% 1.53/1.72      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf(t46_tex_2, axiom,
% 1.53/1.72    (![A:$i]:
% 1.53/1.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.53/1.72       ( ![B:$i]:
% 1.53/1.72         ( ( ( v1_xboole_0 @ B ) & 
% 1.53/1.72             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.53/1.72           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 1.53/1.72  thf('108', plain,
% 1.53/1.72      (![X36 : $i, X37 : $i]:
% 1.53/1.72         (~ (v1_xboole_0 @ X36)
% 1.53/1.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.53/1.72          | ~ (v3_tex_2 @ X36 @ X37)
% 1.53/1.72          | ~ (l1_pre_topc @ X37)
% 1.53/1.72          | ~ (v2_pre_topc @ X37)
% 1.53/1.72          | (v2_struct_0 @ X37))),
% 1.53/1.72      inference('cnf', [status(esa)], [t46_tex_2])).
% 1.53/1.72  thf('109', plain,
% 1.53/1.72      (((v2_struct_0 @ sk_A)
% 1.53/1.72        | ~ (v2_pre_topc @ sk_A)
% 1.53/1.72        | ~ (l1_pre_topc @ sk_A)
% 1.53/1.72        | ~ (v3_tex_2 @ sk_B_3 @ sk_A)
% 1.53/1.72        | ~ (v1_xboole_0 @ sk_B_3))),
% 1.53/1.72      inference('sup-', [status(thm)], ['107', '108'])).
% 1.53/1.72  thf('110', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('112', plain,
% 1.53/1.72      (((v2_struct_0 @ sk_A)
% 1.53/1.72        | ~ (v3_tex_2 @ sk_B_3 @ sk_A)
% 1.53/1.72        | ~ (v1_xboole_0 @ sk_B_3))),
% 1.53/1.72      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.53/1.72  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('114', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ sk_B_3) | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('clc', [status(thm)], ['112', '113'])).
% 1.53/1.72  thf('115', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ sk_B_3)) <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['106', '114'])).
% 1.53/1.72  thf('116', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A) | (v1_zfmisc_1 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['105', '115'])).
% 1.53/1.72  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('118', plain,
% 1.53/1.72      (((v1_zfmisc_1 @ sk_B_3))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['116', '117'])).
% 1.53/1.72  thf('119', plain,
% 1.53/1.72      ((((v2_struct_0 @ sk_A)
% 1.53/1.72         | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['91', '118'])).
% 1.53/1.72  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('121', plain,
% 1.53/1.72      ((((v1_xboole_0 @ sk_B_3) | ((u1_struct_0 @ sk_A) = (k1_xboole_0))))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['119', '120'])).
% 1.53/1.72  thf('122', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ sk_B_3)) <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['106', '114'])).
% 1.53/1.72  thf('123', plain,
% 1.53/1.72      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['121', '122'])).
% 1.53/1.72  thf('124', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_3))),
% 1.53/1.72      inference('sup-', [status(thm)], ['84', '85'])).
% 1.53/1.72  thf('125', plain,
% 1.53/1.72      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_B_3)))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['123', '124'])).
% 1.53/1.72  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.53/1.72      inference('sup-', [status(thm)], ['48', '51'])).
% 1.53/1.72  thf('127', plain,
% 1.53/1.72      (((v1_xboole_0 @ sk_B_3))
% 1.53/1.72         <= (((v3_tex_2 @ sk_B_3 @ sk_A)) & 
% 1.53/1.72             ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['125', '126'])).
% 1.53/1.72  thf('128', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ sk_B_3)) <= (((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['106', '114'])).
% 1.53/1.72  thf('129', plain,
% 1.53/1.72      (~ ((v3_tex_2 @ sk_B_3 @ sk_A)) | 
% 1.53/1.72       ~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['127', '128'])).
% 1.53/1.72  thf('130', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('131', plain,
% 1.53/1.72      (((m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72        | (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['21', '130'])).
% 1.53/1.72  thf('132', plain,
% 1.53/1.72      ((~ (v3_tex_2 @ sk_B_3 @ sk_A)) <= (~ ((v3_tex_2 @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('split', [status(esa)], ['78'])).
% 1.53/1.72  thf('133', plain,
% 1.53/1.72      (~ ((v3_tex_2 @ sk_B_3 @ sk_A)) | 
% 1.53/1.72       ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('split', [status(esa)], ['78'])).
% 1.53/1.72  thf('134', plain, (~ ((v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129', '133'])).
% 1.53/1.72  thf('135', plain, (~ (v3_tex_2 @ sk_B_3 @ sk_A)),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['132', '134'])).
% 1.53/1.72  thf('136', plain,
% 1.53/1.72      ((m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ (k1_zfmisc_1 @ sk_B_3))),
% 1.53/1.72      inference('clc', [status(thm)], ['131', '135'])).
% 1.53/1.72  thf('137', plain,
% 1.53/1.72      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.72  thf('138', plain,
% 1.53/1.72      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('139', plain,
% 1.53/1.72      (((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ sk_B_3)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup+', [status(thm)], ['137', '138'])).
% 1.53/1.72  thf(t8_subset_1, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.72       ( ![C:$i]:
% 1.53/1.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.72           ( ( ![D:$i]:
% 1.53/1.72               ( ( m1_subset_1 @ D @ A ) =>
% 1.53/1.72                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 1.53/1.72             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.53/1.72  thf('140', plain,
% 1.53/1.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.53/1.72          | ((X13) = (X11))
% 1.53/1.72          | (m1_subset_1 @ (sk_D @ X11 @ X13 @ X12) @ X12)
% 1.53/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t8_subset_1])).
% 1.53/1.72  thf('141', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (m1_subset_1 @ (sk_D @ sk_B_3 @ X0 @ sk_B_3) @ sk_B_3)
% 1.53/1.72           | ((X0) = (sk_B_3))))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['139', '140'])).
% 1.53/1.72  thf('142', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('143', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72          | (m1_subset_1 @ (sk_D @ sk_B_3 @ X0 @ sk_B_3) @ sk_B_3)
% 1.53/1.72          | ((X0) = (sk_B_3)))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['141', '142'])).
% 1.53/1.72  thf('144', plain,
% 1.53/1.72      ((((sk_C @ sk_B_3 @ sk_A) = (sk_B_3))
% 1.53/1.72        | (m1_subset_1 @ (sk_D @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72           sk_B_3))),
% 1.53/1.72      inference('sup-', [status(thm)], ['136', '143'])).
% 1.53/1.72  thf('145', plain,
% 1.53/1.72      (((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ sk_B_3)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup+', [status(thm)], ['137', '138'])).
% 1.53/1.72  thf('146', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('147', plain, ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ sk_B_3))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['145', '146'])).
% 1.53/1.72  thf('148', plain,
% 1.53/1.72      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.72  thf('149', plain,
% 1.53/1.72      (![X30 : $i, X31 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.72          | ~ (v2_tex_2 @ X30 @ X31)
% 1.53/1.72          | ((X30) != (sk_C @ X30 @ X31))
% 1.53/1.72          | (v3_tex_2 @ X30 @ X31)
% 1.53/1.72          | ~ (l1_pre_topc @ X31))),
% 1.53/1.72      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.53/1.72  thf('150', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | ~ (l1_pre_topc @ sk_A)
% 1.53/1.72           | (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | ((X0) != (sk_C @ X0 @ sk_A))
% 1.53/1.72           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['148', '149'])).
% 1.53/1.72  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('152', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | ((X0) != (sk_C @ X0 @ sk_A))
% 1.53/1.72           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['150', '151'])).
% 1.53/1.72  thf('153', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('154', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72          | (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72          | ((X0) != (sk_C @ X0 @ sk_A))
% 1.53/1.72          | ~ (v2_tex_2 @ X0 @ sk_A))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['152', '153'])).
% 1.53/1.72  thf('155', plain,
% 1.53/1.72      ((~ (v2_tex_2 @ sk_B_3 @ sk_A)
% 1.53/1.72        | ((sk_B_3) != (sk_C @ sk_B_3 @ sk_A))
% 1.53/1.72        | (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('sup-', [status(thm)], ['147', '154'])).
% 1.53/1.72  thf('156', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.53/1.72      inference('clc', [status(thm)], ['17', '18'])).
% 1.53/1.72  thf('157', plain,
% 1.53/1.72      ((((sk_B_3) != (sk_C @ sk_B_3 @ sk_A)) | (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('demod', [status(thm)], ['155', '156'])).
% 1.53/1.72  thf('158', plain, (~ (v3_tex_2 @ sk_B_3 @ sk_A)),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['132', '134'])).
% 1.53/1.72  thf('159', plain, (((sk_B_3) != (sk_C @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('clc', [status(thm)], ['157', '158'])).
% 1.53/1.72  thf('160', plain,
% 1.53/1.72      ((m1_subset_1 @ (sk_D @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72        sk_B_3)),
% 1.53/1.72      inference('simplify_reflect-', [status(thm)], ['144', '159'])).
% 1.53/1.72  thf('161', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ X1)
% 1.53/1.72          | (r2_hidden @ X0 @ X1)
% 1.53/1.72          | (v1_xboole_0 @ X1))),
% 1.53/1.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.53/1.72  thf('162', plain,
% 1.53/1.72      (((v1_xboole_0 @ sk_B_3)
% 1.53/1.72        | (r2_hidden @ (sk_D @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72           sk_B_3))),
% 1.53/1.72      inference('sup-', [status(thm)], ['160', '161'])).
% 1.53/1.72  thf('163', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf('164', plain,
% 1.53/1.72      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.72  thf('165', plain,
% 1.53/1.72      (![X34 : $i, X35 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.53/1.72          | (v2_tex_2 @ X34 @ X35)
% 1.53/1.72          | ~ (l1_pre_topc @ X35)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X35)
% 1.53/1.72          | ~ (v2_pre_topc @ X35)
% 1.53/1.72          | (v2_struct_0 @ X35))),
% 1.53/1.72      inference('cnf', [status(esa)], [t43_tex_2])).
% 1.53/1.72  thf('166', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (v2_struct_0 @ sk_A)
% 1.53/1.72           | ~ (v2_pre_topc @ sk_A)
% 1.53/1.72           | ~ (v1_tdlat_3 @ sk_A)
% 1.53/1.72           | ~ (l1_pre_topc @ sk_A)
% 1.53/1.72           | (v2_tex_2 @ X0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['164', '165'])).
% 1.53/1.72  thf('167', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('168', plain, ((v1_tdlat_3 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('169', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('170', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (v2_struct_0 @ sk_A)
% 1.53/1.72           | (v2_tex_2 @ X0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['166', '167', '168', '169'])).
% 1.53/1.72  thf('171', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('172', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          ((v2_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['170', '171'])).
% 1.53/1.72  thf('173', plain,
% 1.53/1.72      (((v2_tex_2 @ k1_xboole_0 @ sk_A))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['163', '172'])).
% 1.53/1.72  thf('174', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf('175', plain,
% 1.53/1.72      (![X30 : $i, X31 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.72          | ~ (v2_tex_2 @ X30 @ X31)
% 1.53/1.72          | (m1_subset_1 @ (sk_C @ X30 @ X31) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.72          | (v3_tex_2 @ X30 @ X31)
% 1.53/1.72          | ~ (l1_pre_topc @ X31))),
% 1.53/1.72      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.53/1.72  thf('176', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_pre_topc @ X0)
% 1.53/1.72          | (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.53/1.72          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['174', '175'])).
% 1.53/1.72  thf('177', plain,
% 1.53/1.72      ((((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ 
% 1.53/1.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.53/1.72         | (v3_tex_2 @ k1_xboole_0 @ sk_A)
% 1.53/1.72         | ~ (l1_pre_topc @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['173', '176'])).
% 1.53/1.72  thf('178', plain,
% 1.53/1.72      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.72  thf('179', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('180', plain,
% 1.53/1.72      ((((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72         | (v3_tex_2 @ k1_xboole_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['177', '178', '179'])).
% 1.53/1.72  thf('181', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf('182', plain,
% 1.53/1.72      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.72  thf('183', plain,
% 1.53/1.72      (![X36 : $i, X37 : $i]:
% 1.53/1.72         (~ (v1_xboole_0 @ X36)
% 1.53/1.72          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.53/1.72          | ~ (v3_tex_2 @ X36 @ X37)
% 1.53/1.72          | ~ (l1_pre_topc @ X37)
% 1.53/1.72          | ~ (v2_pre_topc @ X37)
% 1.53/1.72          | (v2_struct_0 @ X37))),
% 1.53/1.72      inference('cnf', [status(esa)], [t46_tex_2])).
% 1.53/1.72  thf('184', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (v2_struct_0 @ sk_A)
% 1.53/1.72           | ~ (v2_pre_topc @ sk_A)
% 1.53/1.72           | ~ (l1_pre_topc @ sk_A)
% 1.53/1.72           | ~ (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | ~ (v1_xboole_0 @ X0)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['182', '183'])).
% 1.53/1.72  thf('185', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('187', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (v2_struct_0 @ sk_A)
% 1.53/1.72           | ~ (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | ~ (v1_xboole_0 @ X0)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.53/1.72  thf('188', plain,
% 1.53/1.72      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.53/1.72         | ~ (v3_tex_2 @ k1_xboole_0 @ sk_A)
% 1.53/1.72         | (v2_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['181', '187'])).
% 1.53/1.72  thf('189', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.53/1.72      inference('sup-', [status(thm)], ['48', '51'])).
% 1.53/1.72  thf('190', plain,
% 1.53/1.72      (((~ (v3_tex_2 @ k1_xboole_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['188', '189'])).
% 1.53/1.72  thf('191', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('192', plain,
% 1.53/1.72      ((~ (v3_tex_2 @ k1_xboole_0 @ sk_A))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['190', '191'])).
% 1.53/1.72  thf('193', plain,
% 1.53/1.72      (((m1_subset_1 @ (sk_C @ k1_xboole_0 @ sk_A) @ (k1_zfmisc_1 @ sk_B_3)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['180', '192'])).
% 1.53/1.72  thf('194', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf('195', plain,
% 1.53/1.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.53/1.72          | ((X13) = (X11))
% 1.53/1.72          | (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X13)
% 1.53/1.72          | (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X11)
% 1.53/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t8_subset_1])).
% 1.53/1.72  thf('196', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.53/1.72          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 1.53/1.72          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 1.53/1.72          | ((X1) = (k1_xboole_0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['194', '195'])).
% 1.53/1.72  thf('197', plain,
% 1.53/1.72      (((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 1.53/1.72         | (r2_hidden @ 
% 1.53/1.72            (sk_D @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72            (sk_C @ k1_xboole_0 @ sk_A))
% 1.53/1.72         | (r2_hidden @ 
% 1.53/1.72            (sk_D @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72            k1_xboole_0)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['193', '196'])).
% 1.53/1.72  thf('198', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf('199', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | ((X0) != (sk_C @ X0 @ sk_A))
% 1.53/1.72           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['150', '151'])).
% 1.53/1.72  thf('200', plain,
% 1.53/1.72      (((~ (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 1.53/1.72         | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))
% 1.53/1.72         | (v3_tex_2 @ k1_xboole_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['198', '199'])).
% 1.53/1.72  thf('201', plain,
% 1.53/1.72      (((v2_tex_2 @ k1_xboole_0 @ sk_A))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['163', '172'])).
% 1.53/1.72  thf('202', plain,
% 1.53/1.72      (((((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A))
% 1.53/1.72         | (v3_tex_2 @ k1_xboole_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['200', '201'])).
% 1.53/1.72  thf('203', plain,
% 1.53/1.72      ((~ (v3_tex_2 @ k1_xboole_0 @ sk_A))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['190', '191'])).
% 1.53/1.72  thf('204', plain,
% 1.53/1.72      ((((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['202', '203'])).
% 1.53/1.72  thf('205', plain,
% 1.53/1.72      ((((r2_hidden @ 
% 1.53/1.72          (sk_D @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72          (sk_C @ k1_xboole_0 @ sk_A))
% 1.53/1.72         | (r2_hidden @ 
% 1.53/1.72            (sk_D @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72            k1_xboole_0)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('simplify_reflect-', [status(thm)], ['197', '204'])).
% 1.53/1.72  thf('206', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('207', plain,
% 1.53/1.72      (((r2_hidden @ 
% 1.53/1.72         (sk_D @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72         (sk_C @ k1_xboole_0 @ sk_A))
% 1.53/1.72        | (r2_hidden @ 
% 1.53/1.72           (sk_D @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72           k1_xboole_0))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['205', '206'])).
% 1.53/1.72  thf('208', plain,
% 1.53/1.72      (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 1.53/1.72      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 1.53/1.72  thf('209', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf('210', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_tarski @ k1_xboole_0))),
% 1.53/1.72      inference('sup+', [status(thm)], ['208', '209'])).
% 1.53/1.72  thf('211', plain,
% 1.53/1.72      (((k1_zfmisc_1 @ k1_xboole_0) = (k1_tarski @ k1_xboole_0))),
% 1.53/1.72      inference('cnf', [status(esa)], [t1_zfmisc_1])).
% 1.53/1.72  thf('212', plain,
% 1.53/1.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.53/1.72         (~ (r2_hidden @ X22 @ X23)
% 1.53/1.72          | ~ (v1_xboole_0 @ X24)
% 1.53/1.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t5_subset])).
% 1.53/1.72  thf('213', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ (k1_tarski @ k1_xboole_0))
% 1.53/1.72          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.53/1.72          | ~ (r2_hidden @ X1 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['211', '212'])).
% 1.53/1.72  thf('214', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.53/1.72      inference('sup-', [status(thm)], ['48', '51'])).
% 1.53/1.72  thf('215', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ (k1_tarski @ k1_xboole_0))
% 1.53/1.72          | ~ (r2_hidden @ X1 @ X0))),
% 1.53/1.72      inference('demod', [status(thm)], ['213', '214'])).
% 1.53/1.72  thf('216', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.53/1.72      inference('sup-', [status(thm)], ['210', '215'])).
% 1.53/1.72  thf('217', plain,
% 1.53/1.72      ((r2_hidden @ 
% 1.53/1.72        (sk_D @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72        (sk_C @ k1_xboole_0 @ sk_A))),
% 1.53/1.72      inference('clc', [status(thm)], ['207', '216'])).
% 1.53/1.72  thf('218', plain,
% 1.53/1.72      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 1.53/1.72      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.53/1.72  thf('219', plain,
% 1.53/1.72      (![X34 : $i, X35 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.53/1.72          | (v2_tex_2 @ X34 @ X35)
% 1.53/1.72          | ~ (l1_pre_topc @ X35)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X35)
% 1.53/1.72          | ~ (v2_pre_topc @ X35)
% 1.53/1.72          | (v2_struct_0 @ X35))),
% 1.53/1.72      inference('cnf', [status(esa)], [t43_tex_2])).
% 1.53/1.72  thf('220', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v2_struct_0 @ X0)
% 1.53/1.72          | ~ (v2_pre_topc @ X0)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X0)
% 1.53/1.72          | ~ (l1_pre_topc @ X0)
% 1.53/1.72          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['218', '219'])).
% 1.53/1.72  thf('221', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_pre_topc @ X0)
% 1.53/1.72          | (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.53/1.72          | ~ (v2_tex_2 @ k1_xboole_0 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['174', '175'])).
% 1.53/1.72  thf('222', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_pre_topc @ X0)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X0)
% 1.53/1.72          | ~ (v2_pre_topc @ X0)
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.53/1.72          | (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.53/1.72          | ~ (l1_pre_topc @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['220', '221'])).
% 1.53/1.72  thf('223', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v3_tex_2 @ k1_xboole_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ~ (v2_pre_topc @ X0)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X0)
% 1.53/1.72          | ~ (l1_pre_topc @ X0))),
% 1.53/1.72      inference('simplify', [status(thm)], ['222'])).
% 1.53/1.72  thf('224', plain,
% 1.53/1.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.53/1.72         (~ (r2_hidden @ X22 @ X23)
% 1.53/1.72          | ~ (v1_xboole_0 @ X24)
% 1.53/1.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t5_subset])).
% 1.53/1.72  thf('225', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         (~ (l1_pre_topc @ X0)
% 1.53/1.72          | ~ (v1_tdlat_3 @ X0)
% 1.53/1.72          | ~ (v2_pre_topc @ X0)
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | (v3_tex_2 @ k1_xboole_0 @ X0)
% 1.53/1.72          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.53/1.72          | ~ (r2_hidden @ X1 @ (sk_C @ k1_xboole_0 @ X0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['223', '224'])).
% 1.53/1.72  thf('226', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.53/1.72        | (v3_tex_2 @ k1_xboole_0 @ sk_A)
% 1.53/1.72        | (v2_struct_0 @ sk_A)
% 1.53/1.72        | ~ (v2_pre_topc @ sk_A)
% 1.53/1.72        | ~ (v1_tdlat_3 @ sk_A)
% 1.53/1.72        | ~ (l1_pre_topc @ sk_A))),
% 1.53/1.72      inference('sup-', [status(thm)], ['217', '225'])).
% 1.53/1.72  thf('227', plain,
% 1.53/1.72      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.72  thf('228', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('229', plain, (((sk_B_3) = (u1_struct_0 @ sk_A))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['227', '228'])).
% 1.53/1.72  thf('230', plain, ((v2_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('231', plain, ((v1_tdlat_3 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('232', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('233', plain,
% 1.53/1.72      ((~ (v1_xboole_0 @ sk_B_3)
% 1.53/1.72        | (v3_tex_2 @ k1_xboole_0 @ sk_A)
% 1.53/1.72        | (v2_struct_0 @ sk_A))),
% 1.53/1.72      inference('demod', [status(thm)], ['226', '229', '230', '231', '232'])).
% 1.53/1.72  thf('234', plain,
% 1.53/1.72      ((~ (v3_tex_2 @ k1_xboole_0 @ sk_A))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('clc', [status(thm)], ['190', '191'])).
% 1.53/1.72  thf('235', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('236', plain, (~ (v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['234', '235'])).
% 1.53/1.72  thf('237', plain, (((v2_struct_0 @ sk_A) | ~ (v1_xboole_0 @ sk_B_3))),
% 1.53/1.72      inference('clc', [status(thm)], ['233', '236'])).
% 1.53/1.72  thf('238', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('239', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 1.53/1.72      inference('clc', [status(thm)], ['237', '238'])).
% 1.53/1.72  thf('240', plain,
% 1.53/1.72      ((r2_hidden @ (sk_D @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A) @ sk_B_3) @ sk_B_3)),
% 1.53/1.72      inference('clc', [status(thm)], ['162', '239'])).
% 1.53/1.72  thf('241', plain, ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ sk_B_3))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['145', '146'])).
% 1.53/1.72  thf('242', plain,
% 1.53/1.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.53/1.72          | ((X13) = (X11))
% 1.53/1.72          | ~ (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X13)
% 1.53/1.72          | ~ (r2_hidden @ (sk_D @ X11 @ X13 @ X12) @ X11)
% 1.53/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t8_subset_1])).
% 1.53/1.72  thf('243', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72          | ~ (r2_hidden @ (sk_D @ sk_B_3 @ X0 @ sk_B_3) @ sk_B_3)
% 1.53/1.72          | ~ (r2_hidden @ (sk_D @ sk_B_3 @ X0 @ sk_B_3) @ X0)
% 1.53/1.72          | ((X0) = (sk_B_3)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['241', '242'])).
% 1.53/1.72  thf('244', plain,
% 1.53/1.72      ((((sk_C @ sk_B_3 @ sk_A) = (sk_B_3))
% 1.53/1.72        | ~ (r2_hidden @ (sk_D @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72             (sk_C @ sk_B_3 @ sk_A))
% 1.53/1.72        | ~ (m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ (k1_zfmisc_1 @ sk_B_3)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['240', '243'])).
% 1.53/1.72  thf('245', plain,
% 1.53/1.72      ((r2_hidden @ (sk_D @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A) @ sk_B_3) @ sk_B_3)),
% 1.53/1.72      inference('clc', [status(thm)], ['162', '239'])).
% 1.53/1.72  thf('246', plain, ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ sk_B_3))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['145', '146'])).
% 1.53/1.72  thf('247', plain,
% 1.53/1.72      ((((sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '4'])).
% 1.53/1.72  thf('248', plain,
% 1.53/1.72      (![X30 : $i, X31 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.53/1.72          | ~ (v2_tex_2 @ X30 @ X31)
% 1.53/1.72          | (r1_tarski @ X30 @ (sk_C @ X30 @ X31))
% 1.53/1.72          | (v3_tex_2 @ X30 @ X31)
% 1.53/1.72          | ~ (l1_pre_topc @ X31))),
% 1.53/1.72      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.53/1.72  thf('249', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | ~ (l1_pre_topc @ sk_A)
% 1.53/1.72           | (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | (r1_tarski @ X0 @ (sk_C @ X0 @ sk_A))
% 1.53/1.72           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('sup-', [status(thm)], ['247', '248'])).
% 1.53/1.72  thf('250', plain, ((l1_pre_topc @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf('251', plain,
% 1.53/1.72      ((![X0 : $i]:
% 1.53/1.72          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72           | (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72           | (r1_tarski @ X0 @ (sk_C @ X0 @ sk_A))
% 1.53/1.72           | ~ (v2_tex_2 @ X0 @ sk_A)))
% 1.53/1.72         <= (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))))),
% 1.53/1.72      inference('demod', [status(thm)], ['249', '250'])).
% 1.53/1.72  thf('252', plain, (~ ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))),
% 1.53/1.72      inference('sat_resolution*', [status(thm)], ['22', '129'])).
% 1.53/1.72  thf('253', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.53/1.72          | (v3_tex_2 @ X0 @ sk_A)
% 1.53/1.72          | (r1_tarski @ X0 @ (sk_C @ X0 @ sk_A))
% 1.53/1.72          | ~ (v2_tex_2 @ X0 @ sk_A))),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['251', '252'])).
% 1.53/1.72  thf('254', plain,
% 1.53/1.72      ((~ (v2_tex_2 @ sk_B_3 @ sk_A)
% 1.53/1.72        | (r1_tarski @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A))
% 1.53/1.72        | (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('sup-', [status(thm)], ['246', '253'])).
% 1.53/1.72  thf('255', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.53/1.72      inference('clc', [status(thm)], ['17', '18'])).
% 1.53/1.72  thf('256', plain,
% 1.53/1.72      (((r1_tarski @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A))
% 1.53/1.72        | (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('demod', [status(thm)], ['254', '255'])).
% 1.53/1.72  thf('257', plain, (~ (v3_tex_2 @ sk_B_3 @ sk_A)),
% 1.53/1.72      inference('simpl_trail', [status(thm)], ['132', '134'])).
% 1.53/1.72  thf('258', plain, ((r1_tarski @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('clc', [status(thm)], ['256', '257'])).
% 1.53/1.72  thf('259', plain,
% 1.53/1.72      (![X16 : $i, X18 : $i]:
% 1.53/1.72         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 1.53/1.72      inference('cnf', [status(esa)], [t3_subset])).
% 1.53/1.72  thf('260', plain,
% 1.53/1.72      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (sk_C @ sk_B_3 @ sk_A)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['258', '259'])).
% 1.53/1.72  thf(l3_subset_1, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.53/1.72  thf('261', plain,
% 1.53/1.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.53/1.72         (~ (r2_hidden @ X4 @ X5)
% 1.53/1.72          | (r2_hidden @ X4 @ X6)
% 1.53/1.72          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 1.53/1.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.53/1.72  thf('262', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((r2_hidden @ X0 @ (sk_C @ sk_B_3 @ sk_A))
% 1.53/1.72          | ~ (r2_hidden @ X0 @ sk_B_3))),
% 1.53/1.72      inference('sup-', [status(thm)], ['260', '261'])).
% 1.53/1.72  thf('263', plain,
% 1.53/1.72      ((r2_hidden @ (sk_D @ sk_B_3 @ (sk_C @ sk_B_3 @ sk_A) @ sk_B_3) @ 
% 1.53/1.72        (sk_C @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('sup-', [status(thm)], ['245', '262'])).
% 1.53/1.72  thf('264', plain,
% 1.53/1.72      ((m1_subset_1 @ (sk_C @ sk_B_3 @ sk_A) @ (k1_zfmisc_1 @ sk_B_3))),
% 1.53/1.72      inference('clc', [status(thm)], ['131', '135'])).
% 1.53/1.72  thf('265', plain, (((sk_C @ sk_B_3 @ sk_A) = (sk_B_3))),
% 1.53/1.72      inference('demod', [status(thm)], ['244', '263', '264'])).
% 1.53/1.72  thf('266', plain, (((sk_B_3) != (sk_C @ sk_B_3 @ sk_A))),
% 1.53/1.72      inference('clc', [status(thm)], ['157', '158'])).
% 1.53/1.72  thf('267', plain, ($false),
% 1.53/1.72      inference('simplify_reflect-', [status(thm)], ['265', '266'])).
% 1.53/1.72  
% 1.53/1.72  % SZS output end Refutation
% 1.53/1.72  
% 1.53/1.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

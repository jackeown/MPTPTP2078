%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jiCKyalerf

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:09 EST 2020

% Result     : Theorem 6.66s
% Output     : Refutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 134 expanded)
%              Number of leaves         :   38 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  615 (1060 expanded)
%              Number of equality atoms :   50 (  61 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(t46_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( v3_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( v3_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('5',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ X24 )
      | ( ( k6_domain_1 @ X24 @ X25 )
        = ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X30 ) @ X29 ) @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t55_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k1_tarski @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t55_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('24',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_tex_2 @ X26 @ X27 )
      | ~ ( v2_tex_2 @ X28 @ X27 )
      | ~ ( r1_tarski @ X26 @ X28 )
      | ( X26 = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf('41',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','43','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['46','47'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('49',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['50','51','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['0','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jiCKyalerf
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.66/6.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.66/6.85  % Solved by: fo/fo7.sh
% 6.66/6.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.66/6.85  % done 4675 iterations in 6.391s
% 6.66/6.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.66/6.85  % SZS output start Refutation
% 6.66/6.85  thf(sk_B_1_type, type, sk_B_1: $i).
% 6.66/6.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.66/6.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.66/6.85  thf(sk_A_type, type, sk_A: $i).
% 6.66/6.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.66/6.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.66/6.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.66/6.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.66/6.85  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 6.66/6.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.66/6.85  thf(sk_B_type, type, sk_B: $i > $i).
% 6.66/6.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.66/6.85  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.66/6.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.66/6.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.66/6.85  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 6.66/6.85  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 6.66/6.85  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.66/6.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 6.66/6.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.66/6.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.66/6.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.66/6.85  thf(t46_tex_2, conjecture,
% 6.66/6.85    (![A:$i]:
% 6.66/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.66/6.85       ( ![B:$i]:
% 6.66/6.85         ( ( ( v1_xboole_0 @ B ) & 
% 6.66/6.85             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.66/6.85           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 6.66/6.85  thf(zf_stmt_0, negated_conjecture,
% 6.66/6.85    (~( ![A:$i]:
% 6.66/6.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.66/6.85            ( l1_pre_topc @ A ) ) =>
% 6.66/6.85          ( ![B:$i]:
% 6.66/6.85            ( ( ( v1_xboole_0 @ B ) & 
% 6.66/6.85                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.66/6.85              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 6.66/6.85    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 6.66/6.85  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf(l13_xboole_0, axiom,
% 6.66/6.85    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.66/6.85  thf('1', plain,
% 6.66/6.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.85      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.66/6.85  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf('4', plain,
% 6.66/6.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.85      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.66/6.85  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['3', '4'])).
% 6.66/6.85  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 6.66/6.85      inference('demod', [status(thm)], ['2', '5'])).
% 6.66/6.85  thf('7', plain,
% 6.66/6.85      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.85      inference('sup+', [status(thm)], ['1', '6'])).
% 6.66/6.85  thf(t6_mcart_1, axiom,
% 6.66/6.85    (![A:$i]:
% 6.66/6.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 6.66/6.85          ( ![B:$i]:
% 6.66/6.85            ( ~( ( r2_hidden @ B @ A ) & 
% 6.66/6.85                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 6.66/6.85                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 6.66/6.85                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 6.66/6.85                       ( r2_hidden @ G @ B ) ) =>
% 6.66/6.85                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 6.66/6.85  thf('8', plain,
% 6.66/6.85      (![X16 : $i]:
% 6.66/6.85         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 6.66/6.85      inference('cnf', [status(esa)], [t6_mcart_1])).
% 6.66/6.85  thf(t1_subset, axiom,
% 6.66/6.85    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 6.66/6.85  thf('9', plain,
% 6.66/6.85      (![X11 : $i, X12 : $i]:
% 6.66/6.85         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 6.66/6.85      inference('cnf', [status(esa)], [t1_subset])).
% 6.66/6.85  thf('10', plain,
% 6.66/6.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['8', '9'])).
% 6.66/6.85  thf(redefinition_k6_domain_1, axiom,
% 6.66/6.85    (![A:$i,B:$i]:
% 6.66/6.85     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 6.66/6.85       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 6.66/6.85  thf('11', plain,
% 6.66/6.85      (![X24 : $i, X25 : $i]:
% 6.66/6.85         ((v1_xboole_0 @ X24)
% 6.66/6.85          | ~ (m1_subset_1 @ X25 @ X24)
% 6.66/6.85          | ((k6_domain_1 @ X24 @ X25) = (k1_tarski @ X25)))),
% 6.66/6.85      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 6.66/6.85  thf('12', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((X0) = (k1_xboole_0))
% 6.66/6.85          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 6.66/6.85          | (v1_xboole_0 @ X0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['10', '11'])).
% 6.66/6.85  thf('13', plain,
% 6.66/6.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.66/6.85      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.66/6.85  thf('14', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 6.66/6.85          | ((X0) = (k1_xboole_0)))),
% 6.66/6.85      inference('clc', [status(thm)], ['12', '13'])).
% 6.66/6.85  thf('15', plain,
% 6.66/6.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['8', '9'])).
% 6.66/6.85  thf(t36_tex_2, axiom,
% 6.66/6.85    (![A:$i]:
% 6.66/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.66/6.85       ( ![B:$i]:
% 6.66/6.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 6.66/6.85           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 6.66/6.85  thf('16', plain,
% 6.66/6.85      (![X29 : $i, X30 : $i]:
% 6.66/6.85         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 6.66/6.85          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X30) @ X29) @ X30)
% 6.66/6.85          | ~ (l1_pre_topc @ X30)
% 6.66/6.85          | ~ (v2_pre_topc @ X30)
% 6.66/6.85          | (v2_struct_0 @ X30))),
% 6.66/6.85      inference('cnf', [status(esa)], [t36_tex_2])).
% 6.66/6.85  thf('17', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 6.66/6.85          | (v2_struct_0 @ X0)
% 6.66/6.85          | ~ (v2_pre_topc @ X0)
% 6.66/6.85          | ~ (l1_pre_topc @ X0)
% 6.66/6.85          | (v2_tex_2 @ 
% 6.66/6.85             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 6.66/6.85             X0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['15', '16'])).
% 6.66/6.85  thf('18', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 6.66/6.85          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 6.66/6.85          | ~ (l1_pre_topc @ X0)
% 6.66/6.85          | ~ (v2_pre_topc @ X0)
% 6.66/6.85          | (v2_struct_0 @ X0)
% 6.66/6.85          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 6.66/6.85      inference('sup+', [status(thm)], ['14', '17'])).
% 6.66/6.85  thf('19', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((v2_struct_0 @ X0)
% 6.66/6.85          | ~ (v2_pre_topc @ X0)
% 6.66/6.85          | ~ (l1_pre_topc @ X0)
% 6.66/6.85          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 6.66/6.85          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 6.66/6.85      inference('simplify', [status(thm)], ['18'])).
% 6.66/6.85  thf('20', plain,
% 6.66/6.85      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['8', '9'])).
% 6.66/6.85  thf(t55_subset_1, axiom,
% 6.66/6.85    (![A:$i,B:$i]:
% 6.66/6.85     ( ( m1_subset_1 @ B @ A ) =>
% 6.66/6.85       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 6.66/6.85         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 6.66/6.85  thf('21', plain,
% 6.66/6.85      (![X9 : $i, X10 : $i]:
% 6.66/6.85         (((X9) = (k1_xboole_0))
% 6.66/6.85          | ~ (m1_subset_1 @ X10 @ X9)
% 6.66/6.85          | (m1_subset_1 @ (k1_tarski @ X10) @ (k1_zfmisc_1 @ X9)))),
% 6.66/6.85      inference('cnf', [status(esa)], [t55_subset_1])).
% 6.66/6.85  thf('22', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((X0) = (k1_xboole_0))
% 6.66/6.85          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 6.66/6.85          | ((X0) = (k1_xboole_0)))),
% 6.66/6.85      inference('sup-', [status(thm)], ['20', '21'])).
% 6.66/6.85  thf('23', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 6.66/6.85          | ((X0) = (k1_xboole_0)))),
% 6.66/6.85      inference('simplify', [status(thm)], ['22'])).
% 6.66/6.85  thf(t4_subset_1, axiom,
% 6.66/6.85    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.66/6.85  thf('24', plain,
% 6.66/6.85      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 6.66/6.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.66/6.85  thf(d7_tex_2, axiom,
% 6.66/6.85    (![A:$i]:
% 6.66/6.85     ( ( l1_pre_topc @ A ) =>
% 6.66/6.85       ( ![B:$i]:
% 6.66/6.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.66/6.85           ( ( v3_tex_2 @ B @ A ) <=>
% 6.66/6.85             ( ( v2_tex_2 @ B @ A ) & 
% 6.66/6.85               ( ![C:$i]:
% 6.66/6.85                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.66/6.85                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 6.66/6.85                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 6.66/6.85  thf('25', plain,
% 6.66/6.85      (![X26 : $i, X27 : $i, X28 : $i]:
% 6.66/6.85         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 6.66/6.85          | ~ (v3_tex_2 @ X26 @ X27)
% 6.66/6.85          | ~ (v2_tex_2 @ X28 @ X27)
% 6.66/6.85          | ~ (r1_tarski @ X26 @ X28)
% 6.66/6.85          | ((X26) = (X28))
% 6.66/6.85          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 6.66/6.85          | ~ (l1_pre_topc @ X27))),
% 6.66/6.85      inference('cnf', [status(esa)], [d7_tex_2])).
% 6.66/6.85  thf('26', plain,
% 6.66/6.85      (![X0 : $i, X1 : $i]:
% 6.66/6.85         (~ (l1_pre_topc @ X0)
% 6.66/6.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.66/6.85          | ((k1_xboole_0) = (X1))
% 6.66/6.85          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 6.66/6.85          | ~ (v2_tex_2 @ X1 @ X0)
% 6.66/6.85          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['24', '25'])).
% 6.66/6.85  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.66/6.85  thf('27', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 6.66/6.85      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.66/6.85  thf('28', plain,
% 6.66/6.85      (![X0 : $i, X1 : $i]:
% 6.66/6.85         (~ (l1_pre_topc @ X0)
% 6.66/6.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.66/6.85          | ((k1_xboole_0) = (X1))
% 6.66/6.85          | ~ (v2_tex_2 @ X1 @ X0)
% 6.66/6.85          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 6.66/6.85      inference('demod', [status(thm)], ['26', '27'])).
% 6.66/6.85  thf('29', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 6.66/6.85          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 6.66/6.85          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 6.66/6.85          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 6.66/6.85          | ~ (l1_pre_topc @ X0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['23', '28'])).
% 6.66/6.85  thf(t4_boole, axiom,
% 6.66/6.85    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 6.66/6.85  thf('30', plain,
% 6.66/6.85      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 6.66/6.85      inference('cnf', [status(esa)], [t4_boole])).
% 6.66/6.85  thf(t98_xboole_1, axiom,
% 6.66/6.85    (![A:$i,B:$i]:
% 6.66/6.85     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.66/6.85  thf('31', plain,
% 6.66/6.85      (![X4 : $i, X5 : $i]:
% 6.66/6.85         ((k2_xboole_0 @ X4 @ X5)
% 6.66/6.85           = (k5_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))),
% 6.66/6.85      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.66/6.85  thf('32', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.66/6.85      inference('sup+', [status(thm)], ['30', '31'])).
% 6.66/6.85  thf(t5_boole, axiom,
% 6.66/6.85    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.66/6.85  thf('33', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 6.66/6.85      inference('cnf', [status(esa)], [t5_boole])).
% 6.66/6.85  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.66/6.85      inference('demod', [status(thm)], ['32', '33'])).
% 6.66/6.85  thf(t49_zfmisc_1, axiom,
% 6.66/6.85    (![A:$i,B:$i]:
% 6.66/6.85     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 6.66/6.85  thf('35', plain,
% 6.66/6.85      (![X6 : $i, X7 : $i]:
% 6.66/6.85         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 6.66/6.85      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 6.66/6.85  thf('36', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['34', '35'])).
% 6.66/6.85  thf('37', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 6.66/6.85          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 6.66/6.85          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 6.66/6.85          | ~ (l1_pre_topc @ X0))),
% 6.66/6.85      inference('simplify_reflect-', [status(thm)], ['29', '36'])).
% 6.66/6.85  thf('38', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 6.66/6.85          | ~ (l1_pre_topc @ X0)
% 6.66/6.85          | ~ (v2_pre_topc @ X0)
% 6.66/6.85          | (v2_struct_0 @ X0)
% 6.66/6.85          | ~ (l1_pre_topc @ X0)
% 6.66/6.85          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 6.66/6.85          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 6.66/6.85      inference('sup-', [status(thm)], ['19', '37'])).
% 6.66/6.85  thf('39', plain,
% 6.66/6.85      (![X0 : $i]:
% 6.66/6.85         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 6.66/6.85          | (v2_struct_0 @ X0)
% 6.66/6.85          | ~ (v2_pre_topc @ X0)
% 6.66/6.85          | ~ (l1_pre_topc @ X0)
% 6.66/6.85          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 6.66/6.85      inference('simplify', [status(thm)], ['38'])).
% 6.66/6.85  thf('40', plain,
% 6.66/6.85      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.66/6.85        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 6.66/6.85        | ~ (l1_pre_topc @ sk_A)
% 6.66/6.85        | ~ (v2_pre_topc @ sk_A)
% 6.66/6.85        | (v2_struct_0 @ sk_A))),
% 6.66/6.85      inference('sup-', [status(thm)], ['7', '39'])).
% 6.66/6.85  thf('41', plain, ((v1_xboole_0 @ sk_B_1)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf('42', plain, (((sk_B_1) = (k1_xboole_0))),
% 6.66/6.85      inference('sup-', [status(thm)], ['3', '4'])).
% 6.66/6.85  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.85      inference('demod', [status(thm)], ['41', '42'])).
% 6.66/6.85  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf('46', plain,
% 6.66/6.85      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 6.66/6.85      inference('demod', [status(thm)], ['40', '43', '44', '45'])).
% 6.66/6.85  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf('48', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 6.66/6.85      inference('clc', [status(thm)], ['46', '47'])).
% 6.66/6.85  thf(fc2_struct_0, axiom,
% 6.66/6.85    (![A:$i]:
% 6.66/6.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 6.66/6.85       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.66/6.85  thf('49', plain,
% 6.66/6.85      (![X23 : $i]:
% 6.66/6.85         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 6.66/6.85          | ~ (l1_struct_0 @ X23)
% 6.66/6.85          | (v2_struct_0 @ X23))),
% 6.66/6.85      inference('cnf', [status(esa)], [fc2_struct_0])).
% 6.66/6.85  thf('50', plain,
% 6.66/6.85      ((~ (v1_xboole_0 @ k1_xboole_0)
% 6.66/6.85        | (v2_struct_0 @ sk_A)
% 6.66/6.85        | ~ (l1_struct_0 @ sk_A))),
% 6.66/6.85      inference('sup-', [status(thm)], ['48', '49'])).
% 6.66/6.85  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.66/6.85      inference('demod', [status(thm)], ['41', '42'])).
% 6.66/6.85  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 6.66/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.66/6.85  thf(dt_l1_pre_topc, axiom,
% 6.66/6.85    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 6.66/6.85  thf('53', plain,
% 6.66/6.85      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 6.66/6.85      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.66/6.85  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 6.66/6.85      inference('sup-', [status(thm)], ['52', '53'])).
% 6.66/6.85  thf('55', plain, ((v2_struct_0 @ sk_A)),
% 6.66/6.85      inference('demod', [status(thm)], ['50', '51', '54'])).
% 6.66/6.85  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 6.66/6.85  
% 6.66/6.85  % SZS output end Refutation
% 6.66/6.85  
% 6.66/6.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

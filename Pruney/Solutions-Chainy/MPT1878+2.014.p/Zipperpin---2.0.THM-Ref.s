%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LGcMctTKm9

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:05 EST 2020

% Result     : Theorem 24.10s
% Output     : Refutation 24.10s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 136 expanded)
%              Number of leaves         :   37 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  609 (1044 expanded)
%              Number of equality atoms :   42 (  59 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    v3_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('12',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('18',plain,(
    ! [X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ X27 )
      | ( ( k6_domain_1 @ X27 @ X28 )
        = ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X33 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X33 ) @ X32 ) @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
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

thf('31',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_tex_2 @ X29 @ X30 )
      | ~ ( v2_tex_2 @ X31 @ X30 )
      | ~ ( r1_tarski @ X29 @ X31 )
      | ( X29 = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( k1_xboole_0 = X1 )
      | ~ ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

thf('40',plain,(
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
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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
    inference(demod,[status(thm)],['42','43','44','45'])).

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
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LGcMctTKm9
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 24.10/24.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.10/24.32  % Solved by: fo/fo7.sh
% 24.10/24.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.10/24.32  % done 26411 iterations in 23.833s
% 24.10/24.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.10/24.32  % SZS output start Refutation
% 24.10/24.32  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 24.10/24.32  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 24.10/24.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.10/24.32  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 24.10/24.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 24.10/24.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 24.10/24.32  thf(sk_B_type, type, sk_B: $i > $i).
% 24.10/24.32  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 24.10/24.32  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 24.10/24.32  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 24.10/24.32  thf(sk_A_type, type, sk_A: $i).
% 24.10/24.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.10/24.32  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 24.10/24.32  thf(sk_B_1_type, type, sk_B_1: $i).
% 24.10/24.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 24.10/24.32  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 24.10/24.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 24.10/24.32  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 24.10/24.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 24.10/24.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 24.10/24.32  thf(t46_tex_2, conjecture,
% 24.10/24.32    (![A:$i]:
% 24.10/24.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 24.10/24.32       ( ![B:$i]:
% 24.10/24.32         ( ( ( v1_xboole_0 @ B ) & 
% 24.10/24.32             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 24.10/24.32           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 24.10/24.32  thf(zf_stmt_0, negated_conjecture,
% 24.10/24.32    (~( ![A:$i]:
% 24.10/24.32        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 24.10/24.32            ( l1_pre_topc @ A ) ) =>
% 24.10/24.32          ( ![B:$i]:
% 24.10/24.32            ( ( ( v1_xboole_0 @ B ) & 
% 24.10/24.32                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 24.10/24.32              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 24.10/24.32    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 24.10/24.32  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 24.10/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.10/24.32  thf(t29_mcart_1, axiom,
% 24.10/24.32    (![A:$i]:
% 24.10/24.32     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 24.10/24.32          ( ![B:$i]:
% 24.10/24.32            ( ~( ( r2_hidden @ B @ A ) & 
% 24.10/24.32                 ( ![C:$i,D:$i,E:$i]:
% 24.10/24.32                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 24.10/24.32                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 24.10/24.32  thf('1', plain,
% 24.10/24.32      (![X21 : $i]:
% 24.10/24.32         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X21) @ X21))),
% 24.10/24.32      inference('cnf', [status(esa)], [t29_mcart_1])).
% 24.10/24.32  thf(d10_xboole_0, axiom,
% 24.10/24.32    (![A:$i,B:$i]:
% 24.10/24.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 24.10/24.32  thf('2', plain,
% 24.10/24.32      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 24.10/24.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.10/24.32  thf('3', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 24.10/24.32      inference('simplify', [status(thm)], ['2'])).
% 24.10/24.32  thf(t3_subset, axiom,
% 24.10/24.32    (![A:$i,B:$i]:
% 24.10/24.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 24.10/24.32  thf('4', plain,
% 24.10/24.32      (![X12 : $i, X14 : $i]:
% 24.10/24.32         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 24.10/24.32      inference('cnf', [status(esa)], [t3_subset])).
% 24.10/24.32  thf('5', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['3', '4'])).
% 24.10/24.32  thf(t5_subset, axiom,
% 24.10/24.32    (![A:$i,B:$i,C:$i]:
% 24.10/24.32     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 24.10/24.32          ( v1_xboole_0 @ C ) ) ))).
% 24.10/24.32  thf('6', plain,
% 24.10/24.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 24.10/24.32         (~ (r2_hidden @ X18 @ X19)
% 24.10/24.32          | ~ (v1_xboole_0 @ X20)
% 24.10/24.32          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 24.10/24.32      inference('cnf', [status(esa)], [t5_subset])).
% 24.10/24.32  thf('7', plain,
% 24.10/24.32      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['5', '6'])).
% 24.10/24.32  thf('8', plain,
% 24.10/24.32      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['1', '7'])).
% 24.10/24.32  thf('9', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 24.10/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.10/24.32  thf('10', plain, ((v1_xboole_0 @ sk_B_1)),
% 24.10/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.10/24.32  thf('11', plain,
% 24.10/24.32      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['1', '7'])).
% 24.10/24.32  thf('12', plain, (((sk_B_1) = (k1_xboole_0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['10', '11'])).
% 24.10/24.32  thf('13', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 24.10/24.32      inference('demod', [status(thm)], ['9', '12'])).
% 24.10/24.32  thf('14', plain,
% 24.10/24.32      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 24.10/24.32      inference('sup+', [status(thm)], ['8', '13'])).
% 24.10/24.32  thf('15', plain,
% 24.10/24.32      (![X21 : $i]:
% 24.10/24.32         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X21) @ X21))),
% 24.10/24.32      inference('cnf', [status(esa)], [t29_mcart_1])).
% 24.10/24.32  thf(t1_subset, axiom,
% 24.10/24.32    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 24.10/24.32  thf('16', plain,
% 24.10/24.32      (![X10 : $i, X11 : $i]:
% 24.10/24.32         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 24.10/24.32      inference('cnf', [status(esa)], [t1_subset])).
% 24.10/24.32  thf('17', plain,
% 24.10/24.32      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['15', '16'])).
% 24.10/24.32  thf(redefinition_k6_domain_1, axiom,
% 24.10/24.32    (![A:$i,B:$i]:
% 24.10/24.32     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 24.10/24.32       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 24.10/24.32  thf('18', plain,
% 24.10/24.32      (![X27 : $i, X28 : $i]:
% 24.10/24.32         ((v1_xboole_0 @ X27)
% 24.10/24.32          | ~ (m1_subset_1 @ X28 @ X27)
% 24.10/24.32          | ((k6_domain_1 @ X27 @ X28) = (k1_tarski @ X28)))),
% 24.10/24.32      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 24.10/24.32  thf('19', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (((X0) = (k1_xboole_0))
% 24.10/24.32          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 24.10/24.32          | (v1_xboole_0 @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['17', '18'])).
% 24.10/24.32  thf('20', plain,
% 24.10/24.32      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['1', '7'])).
% 24.10/24.32  thf('21', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 24.10/24.32          | ((X0) = (k1_xboole_0)))),
% 24.10/24.32      inference('clc', [status(thm)], ['19', '20'])).
% 24.10/24.32  thf('22', plain,
% 24.10/24.32      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['15', '16'])).
% 24.10/24.32  thf(t36_tex_2, axiom,
% 24.10/24.32    (![A:$i]:
% 24.10/24.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 24.10/24.32       ( ![B:$i]:
% 24.10/24.32         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 24.10/24.32           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 24.10/24.32  thf('23', plain,
% 24.10/24.32      (![X32 : $i, X33 : $i]:
% 24.10/24.32         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X33))
% 24.10/24.32          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X33) @ X32) @ X33)
% 24.10/24.32          | ~ (l1_pre_topc @ X33)
% 24.10/24.32          | ~ (v2_pre_topc @ X33)
% 24.10/24.32          | (v2_struct_0 @ X33))),
% 24.10/24.32      inference('cnf', [status(esa)], [t36_tex_2])).
% 24.10/24.32  thf('24', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 24.10/24.32          | (v2_struct_0 @ X0)
% 24.10/24.32          | ~ (v2_pre_topc @ X0)
% 24.10/24.32          | ~ (l1_pre_topc @ X0)
% 24.10/24.32          | (v2_tex_2 @ 
% 24.10/24.32             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 24.10/24.32             X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['22', '23'])).
% 24.10/24.32  thf('25', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 24.10/24.32          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 24.10/24.32          | ~ (l1_pre_topc @ X0)
% 24.10/24.32          | ~ (v2_pre_topc @ X0)
% 24.10/24.32          | (v2_struct_0 @ X0)
% 24.10/24.32          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 24.10/24.32      inference('sup+', [status(thm)], ['21', '24'])).
% 24.10/24.32  thf('26', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         ((v2_struct_0 @ X0)
% 24.10/24.32          | ~ (v2_pre_topc @ X0)
% 24.10/24.32          | ~ (l1_pre_topc @ X0)
% 24.10/24.32          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 24.10/24.32          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 24.10/24.32      inference('simplify', [status(thm)], ['25'])).
% 24.10/24.32  thf('27', plain,
% 24.10/24.32      (![X21 : $i]:
% 24.10/24.32         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X21) @ X21))),
% 24.10/24.32      inference('cnf', [status(esa)], [t29_mcart_1])).
% 24.10/24.32  thf(t63_subset_1, axiom,
% 24.10/24.32    (![A:$i,B:$i]:
% 24.10/24.32     ( ( r2_hidden @ A @ B ) =>
% 24.10/24.32       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 24.10/24.32  thf('28', plain,
% 24.10/24.32      (![X8 : $i, X9 : $i]:
% 24.10/24.32         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 24.10/24.32          | ~ (r2_hidden @ X8 @ X9))),
% 24.10/24.32      inference('cnf', [status(esa)], [t63_subset_1])).
% 24.10/24.32  thf('29', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (((X0) = (k1_xboole_0))
% 24.10/24.32          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 24.10/24.32      inference('sup-', [status(thm)], ['27', '28'])).
% 24.10/24.32  thf(t4_subset_1, axiom,
% 24.10/24.32    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 24.10/24.32  thf('30', plain,
% 24.10/24.32      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 24.10/24.32      inference('cnf', [status(esa)], [t4_subset_1])).
% 24.10/24.32  thf(d7_tex_2, axiom,
% 24.10/24.32    (![A:$i]:
% 24.10/24.32     ( ( l1_pre_topc @ A ) =>
% 24.10/24.32       ( ![B:$i]:
% 24.10/24.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.10/24.32           ( ( v3_tex_2 @ B @ A ) <=>
% 24.10/24.32             ( ( v2_tex_2 @ B @ A ) & 
% 24.10/24.32               ( ![C:$i]:
% 24.10/24.32                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.10/24.32                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 24.10/24.32                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 24.10/24.32  thf('31', plain,
% 24.10/24.32      (![X29 : $i, X30 : $i, X31 : $i]:
% 24.10/24.32         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 24.10/24.32          | ~ (v3_tex_2 @ X29 @ X30)
% 24.10/24.32          | ~ (v2_tex_2 @ X31 @ X30)
% 24.10/24.32          | ~ (r1_tarski @ X29 @ X31)
% 24.10/24.32          | ((X29) = (X31))
% 24.10/24.32          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 24.10/24.32          | ~ (l1_pre_topc @ X30))),
% 24.10/24.32      inference('cnf', [status(esa)], [d7_tex_2])).
% 24.10/24.32  thf('32', plain,
% 24.10/24.32      (![X0 : $i, X1 : $i]:
% 24.10/24.32         (~ (l1_pre_topc @ X0)
% 24.10/24.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 24.10/24.32          | ((k1_xboole_0) = (X1))
% 24.10/24.32          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 24.10/24.32          | ~ (v2_tex_2 @ X1 @ X0)
% 24.10/24.32          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['30', '31'])).
% 24.10/24.32  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 24.10/24.32  thf('33', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 24.10/24.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 24.10/24.32  thf('34', plain,
% 24.10/24.32      (![X0 : $i, X1 : $i]:
% 24.10/24.32         (~ (l1_pre_topc @ X0)
% 24.10/24.32          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 24.10/24.32          | ((k1_xboole_0) = (X1))
% 24.10/24.32          | ~ (v2_tex_2 @ X1 @ X0)
% 24.10/24.32          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 24.10/24.32      inference('demod', [status(thm)], ['32', '33'])).
% 24.10/24.32  thf('35', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 24.10/24.32          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 24.10/24.32          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 24.10/24.32          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 24.10/24.32          | ~ (l1_pre_topc @ X0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['29', '34'])).
% 24.10/24.32  thf(t1_boole, axiom,
% 24.10/24.32    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 24.10/24.32  thf('36', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 24.10/24.32      inference('cnf', [status(esa)], [t1_boole])).
% 24.10/24.32  thf(t49_zfmisc_1, axiom,
% 24.10/24.32    (![A:$i,B:$i]:
% 24.10/24.32     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 24.10/24.32  thf('37', plain,
% 24.10/24.32      (![X5 : $i, X6 : $i]:
% 24.10/24.32         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 24.10/24.32      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 24.10/24.32  thf('38', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 24.10/24.32      inference('sup-', [status(thm)], ['36', '37'])).
% 24.10/24.32  thf('39', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 24.10/24.32          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 24.10/24.32          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 24.10/24.32          | ~ (l1_pre_topc @ X0))),
% 24.10/24.32      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 24.10/24.32  thf('40', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 24.10/24.32          | ~ (l1_pre_topc @ X0)
% 24.10/24.32          | ~ (v2_pre_topc @ X0)
% 24.10/24.32          | (v2_struct_0 @ X0)
% 24.10/24.32          | ~ (l1_pre_topc @ X0)
% 24.10/24.32          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 24.10/24.32          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 24.10/24.32      inference('sup-', [status(thm)], ['26', '39'])).
% 24.10/24.32  thf('41', plain,
% 24.10/24.32      (![X0 : $i]:
% 24.10/24.32         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 24.10/24.32          | (v2_struct_0 @ X0)
% 24.10/24.32          | ~ (v2_pre_topc @ X0)
% 24.10/24.32          | ~ (l1_pre_topc @ X0)
% 24.10/24.32          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 24.10/24.32      inference('simplify', [status(thm)], ['40'])).
% 24.10/24.32  thf('42', plain,
% 24.10/24.32      ((~ (v1_xboole_0 @ k1_xboole_0)
% 24.10/24.32        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 24.10/24.32        | ~ (l1_pre_topc @ sk_A)
% 24.10/24.32        | ~ (v2_pre_topc @ sk_A)
% 24.10/24.32        | (v2_struct_0 @ sk_A))),
% 24.10/24.32      inference('sup-', [status(thm)], ['14', '41'])).
% 24.10/24.32  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 24.10/24.32  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.10/24.32      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.10/24.32  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 24.10/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.10/24.32  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 24.10/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.10/24.32  thf('46', plain,
% 24.10/24.32      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 24.10/24.32      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 24.10/24.32  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 24.10/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.10/24.32  thf('48', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 24.10/24.32      inference('clc', [status(thm)], ['46', '47'])).
% 24.10/24.32  thf(fc2_struct_0, axiom,
% 24.10/24.32    (![A:$i]:
% 24.10/24.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 24.10/24.32       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 24.10/24.32  thf('49', plain,
% 24.10/24.32      (![X26 : $i]:
% 24.10/24.32         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 24.10/24.32          | ~ (l1_struct_0 @ X26)
% 24.10/24.32          | (v2_struct_0 @ X26))),
% 24.10/24.32      inference('cnf', [status(esa)], [fc2_struct_0])).
% 24.10/24.32  thf('50', plain,
% 24.10/24.32      ((~ (v1_xboole_0 @ k1_xboole_0)
% 24.10/24.32        | (v2_struct_0 @ sk_A)
% 24.10/24.32        | ~ (l1_struct_0 @ sk_A))),
% 24.10/24.32      inference('sup-', [status(thm)], ['48', '49'])).
% 24.10/24.32  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 24.10/24.32      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 24.10/24.32  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 24.10/24.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.10/24.32  thf(dt_l1_pre_topc, axiom,
% 24.10/24.32    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 24.10/24.32  thf('53', plain,
% 24.10/24.32      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 24.10/24.32      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 24.10/24.32  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 24.10/24.32      inference('sup-', [status(thm)], ['52', '53'])).
% 24.10/24.32  thf('55', plain, ((v2_struct_0 @ sk_A)),
% 24.10/24.32      inference('demod', [status(thm)], ['50', '51', '54'])).
% 24.10/24.32  thf('56', plain, ($false), inference('demod', [status(thm)], ['0', '55'])).
% 24.10/24.32  
% 24.10/24.32  % SZS output end Refutation
% 24.10/24.32  
% 24.10/24.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

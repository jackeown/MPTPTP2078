%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YNMszWKCSE

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:09 EST 2020

% Result     : Theorem 5.63s
% Output     : Refutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 126 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  575 (1020 expanded)
%              Number of equality atoms :   44 (  55 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( m1_subset_1 @ ( k1_tarski @ X9 ) @ ( k1_zfmisc_1 @ X8 ) ) ) ),
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

thf('25',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_tex_2 @ X25 @ X26 )
      | ~ ( v2_tex_2 @ X27 @ X26 )
      | ~ ( r1_tarski @ X25 @ X27 )
      | ( X25 = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ X2 ) ),
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

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('30',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X5 ) @ X6 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

thf('34',plain,(
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
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','35'])).

thf('37',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['42','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','47','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YNMszWKCSE
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 5.63/5.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.63/5.81  % Solved by: fo/fo7.sh
% 5.63/5.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.63/5.81  % done 3421 iterations in 5.368s
% 5.63/5.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.63/5.81  % SZS output start Refutation
% 5.63/5.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.63/5.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.63/5.81  thf(sk_A_type, type, sk_A: $i).
% 5.63/5.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.63/5.81  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 5.63/5.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.63/5.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.63/5.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.63/5.81  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 5.63/5.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.63/5.81  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 5.63/5.81  thf(sk_B_type, type, sk_B: $i > $i).
% 5.63/5.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.63/5.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.63/5.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.63/5.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.63/5.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.63/5.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.63/5.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.63/5.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.63/5.81  thf(t46_tex_2, conjecture,
% 5.63/5.81    (![A:$i]:
% 5.63/5.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.63/5.81       ( ![B:$i]:
% 5.63/5.81         ( ( ( v1_xboole_0 @ B ) & 
% 5.63/5.81             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.63/5.81           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 5.63/5.81  thf(zf_stmt_0, negated_conjecture,
% 5.63/5.81    (~( ![A:$i]:
% 5.63/5.81        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.63/5.81            ( l1_pre_topc @ A ) ) =>
% 5.63/5.81          ( ![B:$i]:
% 5.63/5.81            ( ( ( v1_xboole_0 @ B ) & 
% 5.63/5.81                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.63/5.81              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 5.63/5.81    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 5.63/5.81  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf(l13_xboole_0, axiom,
% 5.63/5.81    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 5.63/5.81  thf('1', plain,
% 5.63/5.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.63/5.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.63/5.81  thf('2', plain, ((v3_tex_2 @ sk_B_1 @ sk_A)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('3', plain, ((v1_xboole_0 @ sk_B_1)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('4', plain,
% 5.63/5.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.63/5.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.63/5.81  thf('5', plain, (((sk_B_1) = (k1_xboole_0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['3', '4'])).
% 5.63/5.81  thf('6', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 5.63/5.81      inference('demod', [status(thm)], ['2', '5'])).
% 5.63/5.81  thf('7', plain,
% 5.63/5.81      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 5.63/5.81      inference('sup+', [status(thm)], ['1', '6'])).
% 5.63/5.81  thf(t6_mcart_1, axiom,
% 5.63/5.81    (![A:$i]:
% 5.63/5.81     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.63/5.81          ( ![B:$i]:
% 5.63/5.81            ( ~( ( r2_hidden @ B @ A ) & 
% 5.63/5.81                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 5.63/5.81                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 5.63/5.81                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 5.63/5.81                       ( r2_hidden @ G @ B ) ) =>
% 5.63/5.81                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 5.63/5.81  thf('8', plain,
% 5.63/5.81      (![X15 : $i]:
% 5.63/5.81         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X15) @ X15))),
% 5.63/5.81      inference('cnf', [status(esa)], [t6_mcart_1])).
% 5.63/5.81  thf(t1_subset, axiom,
% 5.63/5.81    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 5.63/5.81  thf('9', plain,
% 5.63/5.81      (![X10 : $i, X11 : $i]:
% 5.63/5.81         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 5.63/5.81      inference('cnf', [status(esa)], [t1_subset])).
% 5.63/5.81  thf('10', plain,
% 5.63/5.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['8', '9'])).
% 5.63/5.81  thf(redefinition_k6_domain_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 5.63/5.81       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 5.63/5.81  thf('11', plain,
% 5.63/5.81      (![X23 : $i, X24 : $i]:
% 5.63/5.81         ((v1_xboole_0 @ X23)
% 5.63/5.81          | ~ (m1_subset_1 @ X24 @ X23)
% 5.63/5.81          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 5.63/5.81      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 5.63/5.81  thf('12', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (((X0) = (k1_xboole_0))
% 5.63/5.81          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 5.63/5.81          | (v1_xboole_0 @ X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['10', '11'])).
% 5.63/5.81  thf('13', plain,
% 5.63/5.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.63/5.81      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.63/5.81  thf('14', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 5.63/5.81          | ((X0) = (k1_xboole_0)))),
% 5.63/5.81      inference('clc', [status(thm)], ['12', '13'])).
% 5.63/5.81  thf('15', plain,
% 5.63/5.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['8', '9'])).
% 5.63/5.81  thf(t36_tex_2, axiom,
% 5.63/5.81    (![A:$i]:
% 5.63/5.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.63/5.81       ( ![B:$i]:
% 5.63/5.81         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.63/5.81           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 5.63/5.81  thf('16', plain,
% 5.63/5.81      (![X28 : $i, X29 : $i]:
% 5.63/5.81         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 5.63/5.81          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 5.63/5.81          | ~ (l1_pre_topc @ X29)
% 5.63/5.81          | ~ (v2_pre_topc @ X29)
% 5.63/5.81          | (v2_struct_0 @ X29))),
% 5.63/5.81      inference('cnf', [status(esa)], [t36_tex_2])).
% 5.63/5.81  thf('17', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 5.63/5.81          | (v2_struct_0 @ X0)
% 5.63/5.81          | ~ (v2_pre_topc @ X0)
% 5.63/5.81          | ~ (l1_pre_topc @ X0)
% 5.63/5.81          | (v2_tex_2 @ 
% 5.63/5.81             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 5.63/5.81             X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['15', '16'])).
% 5.63/5.81  thf('18', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 5.63/5.81          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 5.63/5.81          | ~ (l1_pre_topc @ X0)
% 5.63/5.81          | ~ (v2_pre_topc @ X0)
% 5.63/5.81          | (v2_struct_0 @ X0)
% 5.63/5.81          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 5.63/5.81      inference('sup+', [status(thm)], ['14', '17'])).
% 5.63/5.81  thf('19', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         ((v2_struct_0 @ X0)
% 5.63/5.81          | ~ (v2_pre_topc @ X0)
% 5.63/5.81          | ~ (l1_pre_topc @ X0)
% 5.63/5.81          | ((u1_struct_0 @ X0) = (k1_xboole_0))
% 5.63/5.81          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 5.63/5.81      inference('simplify', [status(thm)], ['18'])).
% 5.63/5.81  thf('20', plain,
% 5.63/5.81      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['8', '9'])).
% 5.63/5.81  thf(t55_subset_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( m1_subset_1 @ B @ A ) =>
% 5.63/5.81       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 5.63/5.81         ( m1_subset_1 @ ( k1_tarski @ B ) @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 5.63/5.81  thf('21', plain,
% 5.63/5.81      (![X8 : $i, X9 : $i]:
% 5.63/5.81         (((X8) = (k1_xboole_0))
% 5.63/5.81          | ~ (m1_subset_1 @ X9 @ X8)
% 5.63/5.81          | (m1_subset_1 @ (k1_tarski @ X9) @ (k1_zfmisc_1 @ X8)))),
% 5.63/5.81      inference('cnf', [status(esa)], [t55_subset_1])).
% 5.63/5.81  thf('22', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (((X0) = (k1_xboole_0))
% 5.63/5.81          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 5.63/5.81          | ((X0) = (k1_xboole_0)))),
% 5.63/5.81      inference('sup-', [status(thm)], ['20', '21'])).
% 5.63/5.81  thf('23', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 5.63/5.81          | ((X0) = (k1_xboole_0)))),
% 5.63/5.81      inference('simplify', [status(thm)], ['22'])).
% 5.63/5.81  thf(t4_subset_1, axiom,
% 5.63/5.81    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.63/5.81  thf('24', plain,
% 5.63/5.81      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.63/5.81      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.63/5.81  thf(d7_tex_2, axiom,
% 5.63/5.81    (![A:$i]:
% 5.63/5.81     ( ( l1_pre_topc @ A ) =>
% 5.63/5.81       ( ![B:$i]:
% 5.63/5.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.63/5.81           ( ( v3_tex_2 @ B @ A ) <=>
% 5.63/5.81             ( ( v2_tex_2 @ B @ A ) & 
% 5.63/5.81               ( ![C:$i]:
% 5.63/5.81                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.63/5.81                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 5.63/5.81                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 5.63/5.81  thf('25', plain,
% 5.63/5.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 5.63/5.81         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 5.63/5.81          | ~ (v3_tex_2 @ X25 @ X26)
% 5.63/5.81          | ~ (v2_tex_2 @ X27 @ X26)
% 5.63/5.81          | ~ (r1_tarski @ X25 @ X27)
% 5.63/5.81          | ((X25) = (X27))
% 5.63/5.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 5.63/5.81          | ~ (l1_pre_topc @ X26))),
% 5.63/5.81      inference('cnf', [status(esa)], [d7_tex_2])).
% 5.63/5.81  thf('26', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i]:
% 5.63/5.81         (~ (l1_pre_topc @ X0)
% 5.63/5.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.63/5.81          | ((k1_xboole_0) = (X1))
% 5.63/5.81          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 5.63/5.81          | ~ (v2_tex_2 @ X1 @ X0)
% 5.63/5.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['24', '25'])).
% 5.63/5.81  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.63/5.81  thf('27', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ X2)),
% 5.63/5.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.63/5.81  thf('28', plain,
% 5.63/5.81      (![X0 : $i, X1 : $i]:
% 5.63/5.81         (~ (l1_pre_topc @ X0)
% 5.63/5.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.63/5.81          | ((k1_xboole_0) = (X1))
% 5.63/5.81          | ~ (v2_tex_2 @ X1 @ X0)
% 5.63/5.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 5.63/5.81      inference('demod', [status(thm)], ['26', '27'])).
% 5.63/5.81  thf('29', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 5.63/5.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.63/5.81          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 5.63/5.81          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 5.63/5.81          | ~ (l1_pre_topc @ X0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['23', '28'])).
% 5.63/5.81  thf(t1_boole, axiom,
% 5.63/5.81    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.63/5.81  thf('30', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 5.63/5.81      inference('cnf', [status(esa)], [t1_boole])).
% 5.63/5.81  thf(t49_zfmisc_1, axiom,
% 5.63/5.81    (![A:$i,B:$i]:
% 5.63/5.81     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 5.63/5.81  thf('31', plain,
% 5.63/5.81      (![X5 : $i, X6 : $i]:
% 5.63/5.81         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 5.63/5.81      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 5.63/5.81  thf('32', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['30', '31'])).
% 5.63/5.81  thf('33', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 5.63/5.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.63/5.81          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 5.63/5.81          | ~ (l1_pre_topc @ X0))),
% 5.63/5.81      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 5.63/5.81  thf('34', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (((u1_struct_0 @ X0) = (k1_xboole_0))
% 5.63/5.81          | ~ (l1_pre_topc @ X0)
% 5.63/5.81          | ~ (v2_pre_topc @ X0)
% 5.63/5.81          | (v2_struct_0 @ X0)
% 5.63/5.81          | ~ (l1_pre_topc @ X0)
% 5.63/5.81          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.63/5.81          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 5.63/5.81      inference('sup-', [status(thm)], ['19', '33'])).
% 5.63/5.81  thf('35', plain,
% 5.63/5.81      (![X0 : $i]:
% 5.63/5.81         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.63/5.81          | (v2_struct_0 @ X0)
% 5.63/5.81          | ~ (v2_pre_topc @ X0)
% 5.63/5.81          | ~ (l1_pre_topc @ X0)
% 5.63/5.81          | ((u1_struct_0 @ X0) = (k1_xboole_0)))),
% 5.63/5.81      inference('simplify', [status(thm)], ['34'])).
% 5.63/5.81  thf('36', plain,
% 5.63/5.81      ((~ (v1_xboole_0 @ k1_xboole_0)
% 5.63/5.81        | ((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 5.63/5.81        | ~ (l1_pre_topc @ sk_A)
% 5.63/5.81        | ~ (v2_pre_topc @ sk_A)
% 5.63/5.81        | (v2_struct_0 @ sk_A))),
% 5.63/5.81      inference('sup-', [status(thm)], ['7', '35'])).
% 5.63/5.81  thf('37', plain, ((v1_xboole_0 @ sk_B_1)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('38', plain, (((sk_B_1) = (k1_xboole_0))),
% 5.63/5.81      inference('sup-', [status(thm)], ['3', '4'])).
% 5.63/5.81  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.63/5.81      inference('demod', [status(thm)], ['37', '38'])).
% 5.63/5.81  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('42', plain,
% 5.63/5.81      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 5.63/5.81      inference('demod', [status(thm)], ['36', '39', '40', '41'])).
% 5.63/5.81  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf('44', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 5.63/5.81      inference('clc', [status(thm)], ['42', '43'])).
% 5.63/5.81  thf(fc2_struct_0, axiom,
% 5.63/5.81    (![A:$i]:
% 5.63/5.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 5.63/5.81       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.63/5.81  thf('45', plain,
% 5.63/5.81      (![X22 : $i]:
% 5.63/5.81         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 5.63/5.81          | ~ (l1_struct_0 @ X22)
% 5.63/5.81          | (v2_struct_0 @ X22))),
% 5.63/5.81      inference('cnf', [status(esa)], [fc2_struct_0])).
% 5.63/5.81  thf('46', plain,
% 5.63/5.81      ((~ (v1_xboole_0 @ k1_xboole_0)
% 5.63/5.81        | (v2_struct_0 @ sk_A)
% 5.63/5.81        | ~ (l1_struct_0 @ sk_A))),
% 5.63/5.81      inference('sup-', [status(thm)], ['44', '45'])).
% 5.63/5.81  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.63/5.81      inference('demod', [status(thm)], ['37', '38'])).
% 5.63/5.81  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 5.63/5.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.81  thf(dt_l1_pre_topc, axiom,
% 5.63/5.81    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.63/5.81  thf('49', plain,
% 5.63/5.81      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 5.63/5.81      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.63/5.81  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 5.63/5.81      inference('sup-', [status(thm)], ['48', '49'])).
% 5.63/5.81  thf('51', plain, ((v2_struct_0 @ sk_A)),
% 5.63/5.81      inference('demod', [status(thm)], ['46', '47', '50'])).
% 5.63/5.81  thf('52', plain, ($false), inference('demod', [status(thm)], ['0', '51'])).
% 5.63/5.81  
% 5.63/5.81  % SZS output end Refutation
% 5.63/5.81  
% 5.63/5.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

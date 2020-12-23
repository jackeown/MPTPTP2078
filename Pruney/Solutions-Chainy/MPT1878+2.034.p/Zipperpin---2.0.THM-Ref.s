%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kKlQjRkIiF

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:07 EST 2020

% Result     : Theorem 5.85s
% Output     : Refutation 5.85s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 120 expanded)
%              Number of leaves         :   35 (  51 expanded)
%              Depth                    :   14
%              Number of atoms          :  535 ( 901 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X15 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v3_tex_2 @ sk_B_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v3_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( ( k6_domain_1 @ X21 @ X22 )
        = ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_tex_2 @ X23 @ X24 )
      | ~ ( v2_tex_2 @ X25 @ X24 )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( X23 = X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
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
    ! [X3: $i] :
      ( ( k2_xboole_0 @ X3 @ k1_xboole_0 )
      = X3 ) ),
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
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ ( u1_struct_0 @ X0 ) ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','35'])).

thf('37',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','6'])).

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
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kKlQjRkIiF
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.85/6.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.85/6.02  % Solved by: fo/fo7.sh
% 5.85/6.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.85/6.02  % done 3744 iterations in 5.556s
% 5.85/6.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.85/6.02  % SZS output start Refutation
% 5.85/6.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.85/6.02  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.85/6.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.85/6.02  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.85/6.02  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 5.85/6.02  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.85/6.02  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 5.85/6.02  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 5.85/6.02  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.85/6.02  thf(sk_B_2_type, type, sk_B_2: $i).
% 5.85/6.02  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 5.85/6.02  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 5.85/6.02  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 5.85/6.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.85/6.02  thf(sk_B_type, type, sk_B: $i > $i).
% 5.85/6.02  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.85/6.02  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.85/6.02  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.85/6.02  thf(sk_A_type, type, sk_A: $i).
% 5.85/6.02  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.85/6.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 5.85/6.02  thf(t46_tex_2, conjecture,
% 5.85/6.02    (![A:$i]:
% 5.85/6.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.85/6.02       ( ![B:$i]:
% 5.85/6.02         ( ( ( v1_xboole_0 @ B ) & 
% 5.85/6.02             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.85/6.02           ( ~( v3_tex_2 @ B @ A ) ) ) ) ))).
% 5.85/6.02  thf(zf_stmt_0, negated_conjecture,
% 5.85/6.02    (~( ![A:$i]:
% 5.85/6.02        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 5.85/6.02            ( l1_pre_topc @ A ) ) =>
% 5.85/6.02          ( ![B:$i]:
% 5.85/6.02            ( ( ( v1_xboole_0 @ B ) & 
% 5.85/6.02                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.85/6.02              ( ~( v3_tex_2 @ B @ A ) ) ) ) ) )),
% 5.85/6.02    inference('cnf.neg', [status(esa)], [t46_tex_2])).
% 5.85/6.02  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf(t29_mcart_1, axiom,
% 5.85/6.02    (![A:$i]:
% 5.85/6.02     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.85/6.02          ( ![B:$i]:
% 5.85/6.02            ( ~( ( r2_hidden @ B @ A ) & 
% 5.85/6.02                 ( ![C:$i,D:$i,E:$i]:
% 5.85/6.02                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 5.85/6.02                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 5.85/6.02  thf('1', plain,
% 5.85/6.02      (![X15 : $i]:
% 5.85/6.02         (((X15) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X15) @ X15))),
% 5.85/6.02      inference('cnf', [status(esa)], [t29_mcart_1])).
% 5.85/6.02  thf(d1_xboole_0, axiom,
% 5.85/6.02    (![A:$i]:
% 5.85/6.02     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.85/6.02  thf('2', plain,
% 5.85/6.02      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.85/6.02      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.85/6.02  thf('3', plain,
% 5.85/6.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['1', '2'])).
% 5.85/6.02  thf('4', plain, ((v3_tex_2 @ sk_B_2 @ sk_A)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf('5', plain, ((v1_xboole_0 @ sk_B_2)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf('6', plain,
% 5.85/6.02      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['1', '2'])).
% 5.85/6.02  thf('7', plain, (((sk_B_2) = (k1_xboole_0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['5', '6'])).
% 5.85/6.02  thf('8', plain, ((v3_tex_2 @ k1_xboole_0 @ sk_A)),
% 5.85/6.02      inference('demod', [status(thm)], ['4', '7'])).
% 5.85/6.02  thf('9', plain,
% 5.85/6.02      (![X0 : $i]: ((v3_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 5.85/6.02      inference('sup+', [status(thm)], ['3', '8'])).
% 5.85/6.02  thf('10', plain,
% 5.85/6.02      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.85/6.02      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.85/6.02  thf(t1_subset, axiom,
% 5.85/6.02    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 5.85/6.02  thf('11', plain,
% 5.85/6.02      (![X10 : $i, X11 : $i]:
% 5.85/6.02         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 5.85/6.02      inference('cnf', [status(esa)], [t1_subset])).
% 5.85/6.02  thf('12', plain,
% 5.85/6.02      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['10', '11'])).
% 5.85/6.02  thf(redefinition_k6_domain_1, axiom,
% 5.85/6.02    (![A:$i,B:$i]:
% 5.85/6.02     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 5.85/6.02       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 5.85/6.02  thf('13', plain,
% 5.85/6.02      (![X21 : $i, X22 : $i]:
% 5.85/6.02         ((v1_xboole_0 @ X21)
% 5.85/6.02          | ~ (m1_subset_1 @ X22 @ X21)
% 5.85/6.02          | ((k6_domain_1 @ X21 @ X22) = (k1_tarski @ X22)))),
% 5.85/6.02      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 5.85/6.02  thf('14', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v1_xboole_0 @ X0)
% 5.85/6.02          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 5.85/6.02          | (v1_xboole_0 @ X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['12', '13'])).
% 5.85/6.02  thf('15', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 5.85/6.02          | (v1_xboole_0 @ X0))),
% 5.85/6.02      inference('simplify', [status(thm)], ['14'])).
% 5.85/6.02  thf('16', plain,
% 5.85/6.02      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['10', '11'])).
% 5.85/6.02  thf(t36_tex_2, axiom,
% 5.85/6.02    (![A:$i]:
% 5.85/6.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 5.85/6.02       ( ![B:$i]:
% 5.85/6.02         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.85/6.02           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 5.85/6.02  thf('17', plain,
% 5.85/6.02      (![X26 : $i, X27 : $i]:
% 5.85/6.02         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 5.85/6.02          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 5.85/6.02          | ~ (l1_pre_topc @ X27)
% 5.85/6.02          | ~ (v2_pre_topc @ X27)
% 5.85/6.02          | (v2_struct_0 @ X27))),
% 5.85/6.02      inference('cnf', [status(esa)], [t36_tex_2])).
% 5.85/6.02  thf('18', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 5.85/6.02          | (v2_struct_0 @ X0)
% 5.85/6.02          | ~ (v2_pre_topc @ X0)
% 5.85/6.02          | ~ (l1_pre_topc @ X0)
% 5.85/6.02          | (v2_tex_2 @ 
% 5.85/6.02             (k6_domain_1 @ (u1_struct_0 @ X0) @ (sk_B @ (u1_struct_0 @ X0))) @ 
% 5.85/6.02             X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['16', '17'])).
% 5.85/6.02  thf('19', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 5.85/6.02          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 5.85/6.02          | ~ (l1_pre_topc @ X0)
% 5.85/6.02          | ~ (v2_pre_topc @ X0)
% 5.85/6.02          | (v2_struct_0 @ X0)
% 5.85/6.02          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 5.85/6.02      inference('sup+', [status(thm)], ['15', '18'])).
% 5.85/6.02  thf('20', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v2_struct_0 @ X0)
% 5.85/6.02          | ~ (v2_pre_topc @ X0)
% 5.85/6.02          | ~ (l1_pre_topc @ X0)
% 5.85/6.02          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 5.85/6.02          | (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0))),
% 5.85/6.02      inference('simplify', [status(thm)], ['19'])).
% 5.85/6.02  thf('21', plain,
% 5.85/6.02      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.85/6.02      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.85/6.02  thf(t63_subset_1, axiom,
% 5.85/6.02    (![A:$i,B:$i]:
% 5.85/6.02     ( ( r2_hidden @ A @ B ) =>
% 5.85/6.02       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 5.85/6.02  thf('22', plain,
% 5.85/6.02      (![X8 : $i, X9 : $i]:
% 5.85/6.02         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 5.85/6.02          | ~ (r2_hidden @ X8 @ X9))),
% 5.85/6.02      inference('cnf', [status(esa)], [t63_subset_1])).
% 5.85/6.02  thf('23', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v1_xboole_0 @ X0)
% 5.85/6.02          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 5.85/6.02      inference('sup-', [status(thm)], ['21', '22'])).
% 5.85/6.02  thf(t4_subset_1, axiom,
% 5.85/6.02    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.85/6.02  thf('24', plain,
% 5.85/6.02      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 5.85/6.02      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.85/6.02  thf(d7_tex_2, axiom,
% 5.85/6.02    (![A:$i]:
% 5.85/6.02     ( ( l1_pre_topc @ A ) =>
% 5.85/6.02       ( ![B:$i]:
% 5.85/6.02         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.85/6.02           ( ( v3_tex_2 @ B @ A ) <=>
% 5.85/6.02             ( ( v2_tex_2 @ B @ A ) & 
% 5.85/6.02               ( ![C:$i]:
% 5.85/6.02                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.85/6.02                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 5.85/6.02                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 5.85/6.02  thf('25', plain,
% 5.85/6.02      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.85/6.02         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.85/6.02          | ~ (v3_tex_2 @ X23 @ X24)
% 5.85/6.02          | ~ (v2_tex_2 @ X25 @ X24)
% 5.85/6.02          | ~ (r1_tarski @ X23 @ X25)
% 5.85/6.02          | ((X23) = (X25))
% 5.85/6.02          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 5.85/6.02          | ~ (l1_pre_topc @ X24))),
% 5.85/6.02      inference('cnf', [status(esa)], [d7_tex_2])).
% 5.85/6.02  thf('26', plain,
% 5.85/6.02      (![X0 : $i, X1 : $i]:
% 5.85/6.02         (~ (l1_pre_topc @ X0)
% 5.85/6.02          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.85/6.02          | ((k1_xboole_0) = (X1))
% 5.85/6.02          | ~ (r1_tarski @ k1_xboole_0 @ X1)
% 5.85/6.02          | ~ (v2_tex_2 @ X1 @ X0)
% 5.85/6.02          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['24', '25'])).
% 5.85/6.02  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.85/6.02  thf('27', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 5.85/6.02      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.85/6.02  thf('28', plain,
% 5.85/6.02      (![X0 : $i, X1 : $i]:
% 5.85/6.02         (~ (l1_pre_topc @ X0)
% 5.85/6.02          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.85/6.02          | ((k1_xboole_0) = (X1))
% 5.85/6.02          | ~ (v2_tex_2 @ X1 @ X0)
% 5.85/6.02          | ~ (v3_tex_2 @ k1_xboole_0 @ X0))),
% 5.85/6.02      inference('demod', [status(thm)], ['26', '27'])).
% 5.85/6.02  thf('29', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 5.85/6.02          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.85/6.02          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 5.85/6.02          | ((k1_xboole_0) = (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))))
% 5.85/6.02          | ~ (l1_pre_topc @ X0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['23', '28'])).
% 5.85/6.02  thf(t1_boole, axiom,
% 5.85/6.02    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 5.85/6.02  thf('30', plain, (![X3 : $i]: ((k2_xboole_0 @ X3 @ k1_xboole_0) = (X3))),
% 5.85/6.02      inference('cnf', [status(esa)], [t1_boole])).
% 5.85/6.02  thf(t49_zfmisc_1, axiom,
% 5.85/6.02    (![A:$i,B:$i]:
% 5.85/6.02     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 5.85/6.02  thf('31', plain,
% 5.85/6.02      (![X5 : $i, X6 : $i]:
% 5.85/6.02         ((k2_xboole_0 @ (k1_tarski @ X5) @ X6) != (k1_xboole_0))),
% 5.85/6.02      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 5.85/6.02  thf('32', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['30', '31'])).
% 5.85/6.02  thf('33', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 5.85/6.02          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.85/6.02          | ~ (v2_tex_2 @ (k1_tarski @ (sk_B @ (u1_struct_0 @ X0))) @ X0)
% 5.85/6.02          | ~ (l1_pre_topc @ X0))),
% 5.85/6.02      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 5.85/6.02  thf('34', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 5.85/6.02          | ~ (l1_pre_topc @ X0)
% 5.85/6.02          | ~ (v2_pre_topc @ X0)
% 5.85/6.02          | (v2_struct_0 @ X0)
% 5.85/6.02          | ~ (l1_pre_topc @ X0)
% 5.85/6.02          | ~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.85/6.02          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 5.85/6.02      inference('sup-', [status(thm)], ['20', '33'])).
% 5.85/6.02  thf('35', plain,
% 5.85/6.02      (![X0 : $i]:
% 5.85/6.02         (~ (v3_tex_2 @ k1_xboole_0 @ X0)
% 5.85/6.02          | (v2_struct_0 @ X0)
% 5.85/6.02          | ~ (v2_pre_topc @ X0)
% 5.85/6.02          | ~ (l1_pre_topc @ X0)
% 5.85/6.02          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 5.85/6.02      inference('simplify', [status(thm)], ['34'])).
% 5.85/6.02  thf('36', plain,
% 5.85/6.02      ((~ (v1_xboole_0 @ k1_xboole_0)
% 5.85/6.02        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 5.85/6.02        | ~ (l1_pre_topc @ sk_A)
% 5.85/6.02        | ~ (v2_pre_topc @ sk_A)
% 5.85/6.02        | (v2_struct_0 @ sk_A))),
% 5.85/6.02      inference('sup-', [status(thm)], ['9', '35'])).
% 5.85/6.02  thf('37', plain, ((v1_xboole_0 @ sk_B_2)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf('38', plain, (((sk_B_2) = (k1_xboole_0))),
% 5.85/6.02      inference('sup-', [status(thm)], ['5', '6'])).
% 5.85/6.02  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.85/6.02      inference('demod', [status(thm)], ['37', '38'])).
% 5.85/6.02  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf('42', plain,
% 5.85/6.02      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 5.85/6.02      inference('demod', [status(thm)], ['36', '39', '40', '41'])).
% 5.85/6.02  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf('44', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 5.85/6.02      inference('clc', [status(thm)], ['42', '43'])).
% 5.85/6.02  thf(fc2_struct_0, axiom,
% 5.85/6.02    (![A:$i]:
% 5.85/6.02     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 5.85/6.02       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.85/6.02  thf('45', plain,
% 5.85/6.02      (![X20 : $i]:
% 5.85/6.02         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 5.85/6.02          | ~ (l1_struct_0 @ X20)
% 5.85/6.02          | (v2_struct_0 @ X20))),
% 5.85/6.02      inference('cnf', [status(esa)], [fc2_struct_0])).
% 5.85/6.02  thf('46', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 5.85/6.02      inference('sup-', [status(thm)], ['44', '45'])).
% 5.85/6.02  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 5.85/6.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.85/6.02  thf(dt_l1_pre_topc, axiom,
% 5.85/6.02    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.85/6.02  thf('48', plain,
% 5.85/6.02      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 5.85/6.02      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.85/6.02  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 5.85/6.02      inference('sup-', [status(thm)], ['47', '48'])).
% 5.85/6.02  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 5.85/6.02      inference('demod', [status(thm)], ['46', '49'])).
% 5.85/6.02  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 5.85/6.02  
% 5.85/6.02  % SZS output end Refutation
% 5.85/6.02  
% 5.85/6.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

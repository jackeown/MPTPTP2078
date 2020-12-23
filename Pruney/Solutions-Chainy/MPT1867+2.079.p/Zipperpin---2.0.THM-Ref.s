%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Rr0q83WM4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:37 EST 2020

% Result     : Theorem 10.93s
% Output     : Refutation 10.93s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 127 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  511 ( 965 expanded)
%              Number of equality atoms :   36 (  47 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X20 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X10 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('25',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X24 )
       != ( sk_C @ X21 @ X22 ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X14: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('35',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('45',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','45','46','49'])).

thf('51',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['4','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8Rr0q83WM4
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:33:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 10.93/11.12  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.93/11.12  % Solved by: fo/fo7.sh
% 10.93/11.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.93/11.12  % done 25023 iterations in 10.665s
% 10.93/11.12  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.93/11.12  % SZS output start Refutation
% 10.93/11.12  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 10.93/11.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.93/11.12  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.93/11.12  thf(sk_B_type, type, sk_B: $i).
% 10.93/11.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.93/11.12  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.93/11.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.93/11.12  thf(sk_A_type, type, sk_A: $i).
% 10.93/11.12  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 10.93/11.12  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 10.93/11.12  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 10.93/11.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.93/11.12  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 10.93/11.12  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.93/11.12  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 10.93/11.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.93/11.13  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 10.93/11.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 10.93/11.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.93/11.13  thf(t35_tex_2, conjecture,
% 10.93/11.13    (![A:$i]:
% 10.93/11.13     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.93/11.13       ( ![B:$i]:
% 10.93/11.13         ( ( ( v1_xboole_0 @ B ) & 
% 10.93/11.13             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.93/11.13           ( v2_tex_2 @ B @ A ) ) ) ))).
% 10.93/11.13  thf(zf_stmt_0, negated_conjecture,
% 10.93/11.13    (~( ![A:$i]:
% 10.93/11.13        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 10.93/11.13            ( l1_pre_topc @ A ) ) =>
% 10.93/11.13          ( ![B:$i]:
% 10.93/11.13            ( ( ( v1_xboole_0 @ B ) & 
% 10.93/11.13                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.93/11.13              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 10.93/11.13    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 10.93/11.13  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 10.93/11.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.93/11.13  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 10.93/11.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.93/11.13  thf(l13_xboole_0, axiom,
% 10.93/11.13    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.93/11.13  thf('2', plain,
% 10.93/11.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.93/11.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 10.93/11.13  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['1', '2'])).
% 10.93/11.13  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 10.93/11.13      inference('demod', [status(thm)], ['0', '3'])).
% 10.93/11.13  thf('5', plain,
% 10.93/11.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.93/11.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 10.93/11.13  thf(t4_subset_1, axiom,
% 10.93/11.13    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 10.93/11.13  thf('6', plain,
% 10.93/11.13      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.93/11.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.93/11.13  thf(d5_tex_2, axiom,
% 10.93/11.13    (![A:$i]:
% 10.93/11.13     ( ( l1_pre_topc @ A ) =>
% 10.93/11.13       ( ![B:$i]:
% 10.93/11.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.93/11.13           ( ( v2_tex_2 @ B @ A ) <=>
% 10.93/11.13             ( ![C:$i]:
% 10.93/11.13               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.93/11.13                 ( ~( ( r1_tarski @ C @ B ) & 
% 10.93/11.13                      ( ![D:$i]:
% 10.93/11.13                        ( ( m1_subset_1 @
% 10.93/11.13                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.93/11.13                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 10.93/11.13                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 10.93/11.13                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 10.93/11.13  thf('7', plain,
% 10.93/11.13      (![X21 : $i, X22 : $i]:
% 10.93/11.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.93/11.13          | (r1_tarski @ (sk_C @ X21 @ X22) @ X21)
% 10.93/11.13          | (v2_tex_2 @ X21 @ X22)
% 10.93/11.13          | ~ (l1_pre_topc @ X22))),
% 10.93/11.13      inference('cnf', [status(esa)], [d5_tex_2])).
% 10.93/11.13  thf('8', plain,
% 10.93/11.13      (![X0 : $i]:
% 10.93/11.13         (~ (l1_pre_topc @ X0)
% 10.93/11.13          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['6', '7'])).
% 10.93/11.13  thf(t3_xboole_1, axiom,
% 10.93/11.13    (![A:$i]:
% 10.93/11.13     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.93/11.13  thf('9', plain,
% 10.93/11.13      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 10.93/11.13      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.93/11.13  thf('10', plain,
% 10.93/11.13      (![X0 : $i]:
% 10.93/11.13         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | ~ (l1_pre_topc @ X0)
% 10.93/11.13          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 10.93/11.13      inference('sup-', [status(thm)], ['8', '9'])).
% 10.93/11.13  thf('11', plain,
% 10.93/11.13      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.93/11.13      inference('cnf', [status(esa)], [l13_xboole_0])).
% 10.93/11.13  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 10.93/11.13      inference('demod', [status(thm)], ['0', '3'])).
% 10.93/11.13  thf('13', plain,
% 10.93/11.13      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['11', '12'])).
% 10.93/11.13  thf('14', plain,
% 10.93/11.13      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 10.93/11.13        | ~ (l1_pre_topc @ sk_A)
% 10.93/11.13        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['10', '13'])).
% 10.93/11.13  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 10.93/11.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.93/11.13  thf('16', plain, ((v1_xboole_0 @ sk_B)),
% 10.93/11.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.93/11.13  thf('17', plain, (((sk_B) = (k1_xboole_0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['1', '2'])).
% 10.93/11.13  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.93/11.13      inference('demod', [status(thm)], ['16', '17'])).
% 10.93/11.13  thf('19', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 10.93/11.13      inference('demod', [status(thm)], ['14', '15', '18'])).
% 10.93/11.13  thf('20', plain,
% 10.93/11.13      (![X0 : $i]:
% 10.93/11.13         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 10.93/11.13      inference('sup+', [status(thm)], ['5', '19'])).
% 10.93/11.13  thf(fc10_tops_1, axiom,
% 10.93/11.13    (![A:$i]:
% 10.93/11.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.93/11.13       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 10.93/11.13  thf('21', plain,
% 10.93/11.13      (![X20 : $i]:
% 10.93/11.13         ((v3_pre_topc @ (k2_struct_0 @ X20) @ X20)
% 10.93/11.13          | ~ (l1_pre_topc @ X20)
% 10.93/11.13          | ~ (v2_pre_topc @ X20))),
% 10.93/11.13      inference('cnf', [status(esa)], [fc10_tops_1])).
% 10.93/11.13  thf(d3_struct_0, axiom,
% 10.93/11.13    (![A:$i]:
% 10.93/11.13     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 10.93/11.13  thf('22', plain,
% 10.93/11.13      (![X18 : $i]:
% 10.93/11.13         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 10.93/11.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.93/11.13  thf(dt_k2_subset_1, axiom,
% 10.93/11.13    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 10.93/11.13  thf('23', plain,
% 10.93/11.13      (![X10 : $i]: (m1_subset_1 @ (k2_subset_1 @ X10) @ (k1_zfmisc_1 @ X10))),
% 10.93/11.13      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 10.93/11.13  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 10.93/11.13  thf('24', plain, (![X9 : $i]: ((k2_subset_1 @ X9) = (X9))),
% 10.93/11.13      inference('cnf', [status(esa)], [d4_subset_1])).
% 10.93/11.13  thf('25', plain, (![X10 : $i]: (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X10))),
% 10.93/11.13      inference('demod', [status(thm)], ['23', '24'])).
% 10.93/11.13  thf('26', plain,
% 10.93/11.13      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.93/11.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.93/11.13  thf('27', plain,
% 10.93/11.13      (![X21 : $i, X22 : $i, X24 : $i]:
% 10.93/11.13         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.93/11.13          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.93/11.13          | ~ (v3_pre_topc @ X24 @ X22)
% 10.93/11.13          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X24)
% 10.93/11.13              != (sk_C @ X21 @ X22))
% 10.93/11.13          | (v2_tex_2 @ X21 @ X22)
% 10.93/11.13          | ~ (l1_pre_topc @ X22))),
% 10.93/11.13      inference('cnf', [status(esa)], [d5_tex_2])).
% 10.93/11.13  thf('28', plain,
% 10.93/11.13      (![X0 : $i, X1 : $i]:
% 10.93/11.13         (~ (l1_pre_topc @ X0)
% 10.93/11.13          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 10.93/11.13              != (sk_C @ k1_xboole_0 @ X0))
% 10.93/11.13          | ~ (v3_pre_topc @ X1 @ X0)
% 10.93/11.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 10.93/11.13      inference('sup-', [status(thm)], ['26', '27'])).
% 10.93/11.13  thf('29', plain,
% 10.93/11.13      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.93/11.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.93/11.13  thf(commutativity_k9_subset_1, axiom,
% 10.93/11.13    (![A:$i,B:$i,C:$i]:
% 10.93/11.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.93/11.13       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 10.93/11.13  thf('30', plain,
% 10.93/11.13      (![X6 : $i, X7 : $i, X8 : $i]:
% 10.93/11.13         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 10.93/11.13          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 10.93/11.13      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 10.93/11.13  thf('31', plain,
% 10.93/11.13      (![X0 : $i, X1 : $i]:
% 10.93/11.13         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 10.93/11.13           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 10.93/11.13      inference('sup-', [status(thm)], ['29', '30'])).
% 10.93/11.13  thf('32', plain,
% 10.93/11.13      (![X14 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X14))),
% 10.93/11.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.93/11.13  thf(redefinition_k9_subset_1, axiom,
% 10.93/11.13    (![A:$i,B:$i,C:$i]:
% 10.93/11.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.93/11.13       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 10.93/11.13  thf('33', plain,
% 10.93/11.13      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.93/11.13         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 10.93/11.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 10.93/11.13      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 10.93/11.13  thf('34', plain,
% 10.93/11.13      (![X0 : $i, X1 : $i]:
% 10.93/11.13         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 10.93/11.13           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['32', '33'])).
% 10.93/11.13  thf(t2_boole, axiom,
% 10.93/11.13    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 10.93/11.13  thf('35', plain,
% 10.93/11.13      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.93/11.13      inference('cnf', [status(esa)], [t2_boole])).
% 10.93/11.13  thf('36', plain,
% 10.93/11.13      (![X0 : $i, X1 : $i]:
% 10.93/11.13         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 10.93/11.13      inference('demod', [status(thm)], ['34', '35'])).
% 10.93/11.13  thf('37', plain,
% 10.93/11.13      (![X0 : $i, X1 : $i]:
% 10.93/11.13         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 10.93/11.13      inference('demod', [status(thm)], ['31', '36'])).
% 10.93/11.13  thf('38', plain,
% 10.93/11.13      (![X0 : $i, X1 : $i]:
% 10.93/11.13         (~ (l1_pre_topc @ X0)
% 10.93/11.13          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 10.93/11.13          | ~ (v3_pre_topc @ X1 @ X0)
% 10.93/11.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 10.93/11.13      inference('demod', [status(thm)], ['28', '37'])).
% 10.93/11.13  thf('39', plain,
% 10.93/11.13      (![X0 : $i]:
% 10.93/11.13         (~ (v3_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 10.93/11.13          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 10.93/11.13          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | ~ (l1_pre_topc @ X0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['25', '38'])).
% 10.93/11.13  thf('40', plain,
% 10.93/11.13      (![X0 : $i]:
% 10.93/11.13         (~ (v3_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 10.93/11.13          | ~ (l1_struct_0 @ X0)
% 10.93/11.13          | ~ (l1_pre_topc @ X0)
% 10.93/11.13          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 10.93/11.13      inference('sup-', [status(thm)], ['22', '39'])).
% 10.93/11.13  thf('41', plain,
% 10.93/11.13      (![X0 : $i]:
% 10.93/11.13         (~ (v2_pre_topc @ X0)
% 10.93/11.13          | ~ (l1_pre_topc @ X0)
% 10.93/11.13          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 10.93/11.13          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | ~ (l1_pre_topc @ X0)
% 10.93/11.13          | ~ (l1_struct_0 @ X0))),
% 10.93/11.13      inference('sup-', [status(thm)], ['21', '40'])).
% 10.93/11.13  thf('42', plain,
% 10.93/11.13      (![X0 : $i]:
% 10.93/11.13         (~ (l1_struct_0 @ X0)
% 10.93/11.13          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.93/11.13          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 10.93/11.13          | ~ (l1_pre_topc @ X0)
% 10.93/11.13          | ~ (v2_pre_topc @ X0))),
% 10.93/11.13      inference('simplify', [status(thm)], ['41'])).
% 10.93/11.13  thf('43', plain,
% 10.93/11.13      ((((k1_xboole_0) != (k1_xboole_0))
% 10.93/11.13        | ~ (v1_xboole_0 @ k1_xboole_0)
% 10.93/11.13        | ~ (v2_pre_topc @ sk_A)
% 10.93/11.13        | ~ (l1_pre_topc @ sk_A)
% 10.93/11.13        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 10.93/11.13        | ~ (l1_struct_0 @ sk_A))),
% 10.93/11.13      inference('sup-', [status(thm)], ['20', '42'])).
% 10.93/11.13  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.93/11.13      inference('demod', [status(thm)], ['16', '17'])).
% 10.93/11.13  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 10.93/11.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.93/11.13  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 10.93/11.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.93/11.13  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 10.93/11.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.93/11.13  thf(dt_l1_pre_topc, axiom,
% 10.93/11.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 10.93/11.13  thf('48', plain,
% 10.93/11.13      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 10.93/11.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.93/11.13  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 10.93/11.13      inference('sup-', [status(thm)], ['47', '48'])).
% 10.93/11.13  thf('50', plain,
% 10.93/11.13      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 10.93/11.13      inference('demod', [status(thm)], ['43', '44', '45', '46', '49'])).
% 10.93/11.13  thf('51', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 10.93/11.13      inference('simplify', [status(thm)], ['50'])).
% 10.93/11.13  thf('52', plain, ($false), inference('demod', [status(thm)], ['4', '51'])).
% 10.93/11.13  
% 10.93/11.13  % SZS output end Refutation
% 10.93/11.13  
% 10.93/11.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

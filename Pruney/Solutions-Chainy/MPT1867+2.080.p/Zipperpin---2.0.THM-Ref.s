%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UyD9PobBYN

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:37 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 127 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  511 ( 965 expanded)
%              Number of equality atoms :   36 (  47 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d6_tex_2,axiom,(
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
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( r1_tarski @ ( sk_C @ X20 @ X21 ) @ X20 )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
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

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X19: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X19 ) @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( ( ( k2_struct_0 @ X17 )
        = ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('25',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X23 )
       != ( sk_C @ X20 @ X21 ) )
      | ( v2_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['28','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k2_struct_0 @ X0 ) @ X0 )
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
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UyD9PobBYN
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 665 iterations in 0.237s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.68  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.49/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.49/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.68  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.49/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.49/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.49/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.49/0.68  thf(t35_tex_2, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( ( v1_xboole_0 @ B ) & 
% 0.49/0.68             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.68           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.49/0.68            ( l1_pre_topc @ A ) ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( ( v1_xboole_0 @ B ) & 
% 0.49/0.68                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.49/0.68              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.49/0.68  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(l13_xboole_0, axiom,
% 0.49/0.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.68  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf(t4_subset_1, axiom,
% 0.49/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.68  thf(d6_tex_2, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_pre_topc @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68           ( ( v2_tex_2 @ B @ A ) <=>
% 0.49/0.68             ( ![C:$i]:
% 0.49/0.68               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.49/0.68                      ( ![D:$i]:
% 0.49/0.68                        ( ( m1_subset_1 @
% 0.49/0.68                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.49/0.68                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.49/0.68                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (![X20 : $i, X21 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.49/0.68          | (r1_tarski @ (sk_C @ X20 @ X21) @ X20)
% 0.49/0.68          | (v2_tex_2 @ X20 @ X21)
% 0.49/0.68          | ~ (l1_pre_topc @ X21))),
% 0.49/0.68      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.49/0.68  thf('8', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (l1_pre_topc @ X0)
% 0.49/0.68          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf(t3_xboole_1, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | ~ (l1_pre_topc @ X0)
% 0.49/0.68          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.68  thf('12', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['10', '13'])).
% 0.49/0.68  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('16', plain, ((v1_xboole_0 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('17', plain, (((sk_B) = (k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.68  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.49/0.68  thf('19', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['14', '15', '18'])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['5', '19'])).
% 0.49/0.68  thf(fc4_pre_topc, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.49/0.68       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X19 : $i]:
% 0.49/0.68         ((v4_pre_topc @ (k2_struct_0 @ X19) @ X19)
% 0.49/0.68          | ~ (l1_pre_topc @ X19)
% 0.49/0.68          | ~ (v2_pre_topc @ X19))),
% 0.49/0.68      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.49/0.68  thf(d3_struct_0, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X17 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X17) = (u1_struct_0 @ X17)) | ~ (l1_struct_0 @ X17))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf(dt_k2_subset_1, axiom,
% 0.49/0.68    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.49/0.68  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.49/0.68  thf('24', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.49/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.49/0.68  thf('25', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.49/0.68      inference('demod', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.49/0.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.49/0.68          | ~ (v4_pre_topc @ X23 @ X21)
% 0.49/0.68          | ((k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X23)
% 0.49/0.68              != (sk_C @ X20 @ X21))
% 0.49/0.68          | (v2_tex_2 @ X20 @ X21)
% 0.49/0.68          | ~ (l1_pre_topc @ X21))),
% 0.49/0.68      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (l1_pre_topc @ X0)
% 0.49/0.68          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.49/0.68              != (sk_C @ k1_xboole_0 @ X0))
% 0.49/0.68          | ~ (v4_pre_topc @ X1 @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.68  thf(commutativity_k9_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.68         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.49/0.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.49/0.68           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.68  thf(redefinition_k9_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.68         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.49/0.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.49/0.68  thf('34', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.49/0.68           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.68  thf(t2_boole, axiom,
% 0.49/0.68    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.68  thf('35', plain,
% 0.49/0.68      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.68      inference('demod', [status(thm)], ['34', '35'])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.49/0.68      inference('demod', [status(thm)], ['31', '36'])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (l1_pre_topc @ X0)
% 0.49/0.68          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.49/0.68          | ~ (v4_pre_topc @ X1 @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '37'])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.49/0.68          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.49/0.68          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | ~ (l1_pre_topc @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['25', '38'])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v4_pre_topc @ (k2_struct_0 @ X0) @ X0)
% 0.49/0.68          | ~ (l1_struct_0 @ X0)
% 0.49/0.68          | ~ (l1_pre_topc @ X0)
% 0.49/0.68          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['22', '39'])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (v2_pre_topc @ X0)
% 0.49/0.68          | ~ (l1_pre_topc @ X0)
% 0.49/0.68          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.49/0.68          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | ~ (l1_pre_topc @ X0)
% 0.49/0.68          | ~ (l1_struct_0 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['21', '40'])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (l1_struct_0 @ X0)
% 0.49/0.68          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.49/0.68          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.49/0.68          | ~ (l1_pre_topc @ X0)
% 0.49/0.68          | ~ (v2_pre_topc @ X0))),
% 0.49/0.68      inference('simplify', [status(thm)], ['41'])).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.68        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.68        | ~ (v2_pre_topc @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.49/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['20', '42'])).
% 0.49/0.68  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.49/0.68  thf('45', plain, ((v2_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_l1_pre_topc, axiom,
% 0.49/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.49/0.68  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['43', '44', '45', '46', '49'])).
% 0.49/0.68  thf('51', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.49/0.68      inference('simplify', [status(thm)], ['50'])).
% 0.49/0.68  thf('52', plain, ($false), inference('demod', [status(thm)], ['4', '51'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

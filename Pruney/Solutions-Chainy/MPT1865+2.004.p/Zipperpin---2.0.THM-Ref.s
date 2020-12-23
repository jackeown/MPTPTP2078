%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6XnvjvhCHi

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:21 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 202 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  617 (2767 expanded)
%              Number of equality atoms :   19 (  91 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t33_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( v4_pre_topc @ D @ A )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( k2_tarski @ X7 @ X7 )
      = ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( m1_subset_1 @ ( sk_D @ X19 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X21: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X21 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X21 @ sk_A )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( v4_pre_topc @ ( sk_D @ X19 @ X17 @ X18 ) @ X18 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('39',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ ( sk_D @ X19 @ X17 @ X18 ) )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('49',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ( k1_tarski @ sk_C_1 )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','39','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6XnvjvhCHi
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 582 iterations in 0.211s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(t33_tex_2, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v2_tex_2 @ B @ A ) =>
% 0.45/0.66             ( ![C:$i]:
% 0.45/0.66               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.66                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.45/0.66                      ( ![D:$i]:
% 0.45/0.66                        ( ( m1_subset_1 @
% 0.45/0.66                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.45/0.66                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.45/0.66                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( l1_pre_topc @ A ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66              ( ( v2_tex_2 @ B @ A ) =>
% 0.45/0.66                ( ![C:$i]:
% 0.45/0.66                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.66                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.45/0.66                         ( ![D:$i]:
% 0.45/0.66                           ( ( m1_subset_1 @
% 0.45/0.66                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.45/0.66                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.45/0.66                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.45/0.66  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t38_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.45/0.66       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.45/0.66         ((r1_tarski @ (k2_tarski @ X8 @ X10) @ X11)
% 0.45/0.66          | ~ (r2_hidden @ X10 @ X11)
% 0.45/0.66          | ~ (r2_hidden @ X8 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X0 @ sk_B)
% 0.45/0.66          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.66  thf(t69_enumset1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.66  thf('5', plain, (![X7 : $i]: ((k2_tarski @ X7 @ X7) = (k1_tarski @ X7))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.45/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf(t28_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (k1_tarski @ sk_C_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)) = (k1_tarski @ sk_C_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(t3_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('13', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf(t108_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k3_xboole_0 @ X2 @ X4) @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X14 : $i, X16 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.45/0.66          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['10', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(d6_tex_2, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_pre_topc @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66           ( ( v2_tex_2 @ B @ A ) <=>
% 0.45/0.66             ( ![C:$i]:
% 0.45/0.66               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.45/0.66                      ( ![D:$i]:
% 0.45/0.66                        ( ( m1_subset_1 @
% 0.45/0.66                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.66                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.45/0.66                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.45/0.66                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (v2_tex_2 @ X17 @ X18)
% 0.45/0.66          | (m1_subset_1 @ (sk_D @ X19 @ X17 @ X18) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (r1_tarski @ X19 @ X17)
% 0.45/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (l1_pre_topc @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ sk_A)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | ~ (r1_tarski @ X0 @ sk_B)
% 0.45/0.66          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('23', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | ~ (r1_tarski @ X0 @ sk_B)
% 0.45/0.66          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['18', '24'])).
% 0.45/0.66  thf('26', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.45/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X21 : $i]:
% 0.45/0.66         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X21)
% 0.45/0.66            != (k1_tarski @ sk_C_1))
% 0.45/0.66          | ~ (v4_pre_topc @ X21 @ sk_A)
% 0.45/0.66          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.45/0.66        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.45/0.66            != (k1_tarski @ sk_C_1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['10', '17'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (v2_tex_2 @ X17 @ X18)
% 0.45/0.66          | (v4_pre_topc @ (sk_D @ X19 @ X17 @ X18) @ X18)
% 0.45/0.66          | ~ (r1_tarski @ X19 @ X17)
% 0.45/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (l1_pre_topc @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ sk_A)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | ~ (r1_tarski @ X0 @ sk_B)
% 0.45/0.66          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.45/0.66          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.66  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('35', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | ~ (r1_tarski @ X0 @ sk_B)
% 0.45/0.66          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.45/0.66        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['30', '36'])).
% 0.45/0.66  thf('38', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.45/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.45/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['10', '17'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (v2_tex_2 @ X17 @ X18)
% 0.45/0.66          | ((k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ 
% 0.45/0.66              (sk_D @ X19 @ X17 @ X18)) = (X19))
% 0.45/0.66          | ~ (r1_tarski @ X19 @ X17)
% 0.45/0.66          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.45/0.66          | ~ (l1_pre_topc @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (l1_pre_topc @ sk_A)
% 0.45/0.66          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | ~ (r1_tarski @ X0 @ sk_B)
% 0.45/0.66          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.45/0.66          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('45', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.66          | ~ (r1_tarski @ X0 @ sk_B)
% 0.45/0.66          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.45/0.66        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['40', '46'])).
% 0.45/0.66  thf('48', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.45/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.45/0.66         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain, (((k1_tarski @ sk_C_1) != (k1_tarski @ sk_C_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['29', '39', '49'])).
% 0.45/0.66  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

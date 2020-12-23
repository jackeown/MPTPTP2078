%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vyca0Gidab

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:23 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 153 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  582 (2335 expanded)
%              Number of equality atoms :   17 (  73 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X3 ) @ X5 )
      | ~ ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('13',plain,(
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

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X16 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X16 @ sk_A )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v4_pre_topc @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('33',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ ( sk_D @ X14 @ X12 @ X13 ) )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('43',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_tarski @ sk_C_1 )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','33','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vyca0Gidab
% 0.15/0.38  % Computer   : n001.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 18:05:00 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.25/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.55  % Solved by: fo/fo7.sh
% 0.25/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.55  % done 72 iterations in 0.056s
% 0.25/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.55  % SZS output start Refutation
% 0.25/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.25/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.25/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.25/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.25/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.25/0.55  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.25/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.25/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.25/0.55  thf(t33_tex_2, conjecture,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ( v2_tex_2 @ B @ A ) =>
% 0.25/0.55             ( ![C:$i]:
% 0.25/0.55               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.55                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.25/0.55                      ( ![D:$i]:
% 0.25/0.55                        ( ( m1_subset_1 @
% 0.25/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.25/0.55                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.25/0.55                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.55    (~( ![A:$i]:
% 0.25/0.55        ( ( l1_pre_topc @ A ) =>
% 0.25/0.55          ( ![B:$i]:
% 0.25/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55              ( ( v2_tex_2 @ B @ A ) =>
% 0.25/0.55                ( ![C:$i]:
% 0.25/0.55                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.55                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.25/0.55                         ( ![D:$i]:
% 0.25/0.55                           ( ( m1_subset_1 @
% 0.25/0.55                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.25/0.55                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.25/0.55                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.25/0.55    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.25/0.55  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(l1_zfmisc_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.25/0.55  thf('1', plain,
% 0.25/0.55      (![X3 : $i, X5 : $i]:
% 0.25/0.55         ((r1_tarski @ (k1_tarski @ X3) @ X5) | ~ (r2_hidden @ X3 @ X5))),
% 0.25/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.25/0.55  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.25/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.55  thf(t28_xboole_1, axiom,
% 0.25/0.55    (![A:$i,B:$i]:
% 0.25/0.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.25/0.55  thf('3', plain,
% 0.25/0.55      (![X0 : $i, X1 : $i]:
% 0.25/0.55         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.25/0.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.25/0.55  thf('4', plain,
% 0.25/0.55      (((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (k1_tarski @ sk_C_1))),
% 0.25/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.25/0.55  thf('5', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(dt_k9_subset_1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.55       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.25/0.55  thf('6', plain,
% 0.25/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.25/0.55         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.25/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.25/0.55      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.25/0.55  thf('7', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.25/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.25/0.55  thf('8', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(redefinition_k9_subset_1, axiom,
% 0.25/0.55    (![A:$i,B:$i,C:$i]:
% 0.25/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.25/0.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.25/0.55  thf('9', plain,
% 0.25/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.25/0.55         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.25/0.55          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.25/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.25/0.55  thf('10', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.25/0.55           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.25/0.55  thf('11', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.25/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('demod', [status(thm)], ['7', '10'])).
% 0.25/0.55  thf('12', plain,
% 0.25/0.55      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('sup+', [status(thm)], ['4', '11'])).
% 0.25/0.55  thf('13', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf(d6_tex_2, axiom,
% 0.25/0.55    (![A:$i]:
% 0.25/0.55     ( ( l1_pre_topc @ A ) =>
% 0.25/0.55       ( ![B:$i]:
% 0.25/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55           ( ( v2_tex_2 @ B @ A ) <=>
% 0.25/0.55             ( ![C:$i]:
% 0.25/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.25/0.55                      ( ![D:$i]:
% 0.25/0.55                        ( ( m1_subset_1 @
% 0.25/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.55                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.25/0.55                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.25/0.55                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.25/0.55  thf('14', plain,
% 0.25/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (v2_tex_2 @ X12 @ X13)
% 0.25/0.55          | (m1_subset_1 @ (sk_D @ X14 @ X12 @ X13) @ 
% 0.25/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (r1_tarski @ X14 @ X12)
% 0.25/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (l1_pre_topc @ X13))),
% 0.25/0.55      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.25/0.55  thf('15', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (l1_pre_topc @ sk_A)
% 0.25/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.25/0.55          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.25/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.25/0.55  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('17', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('18', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.25/0.55          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.25/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.25/0.55  thf('19', plain,
% 0.25/0.55      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.25/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['12', '18'])).
% 0.25/0.55  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.25/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.55  thf('21', plain,
% 0.25/0.55      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.25/0.55  thf('22', plain,
% 0.25/0.55      (![X16 : $i]:
% 0.25/0.55         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X16)
% 0.25/0.55            != (k1_tarski @ sk_C_1))
% 0.25/0.55          | ~ (v4_pre_topc @ X16 @ sk_A)
% 0.25/0.55          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('23', plain,
% 0.25/0.55      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.25/0.55        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.25/0.55            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.25/0.55            != (k1_tarski @ sk_C_1)))),
% 0.25/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.25/0.55  thf('24', plain,
% 0.25/0.55      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('sup+', [status(thm)], ['4', '11'])).
% 0.25/0.55  thf('25', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('26', plain,
% 0.25/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (v2_tex_2 @ X12 @ X13)
% 0.25/0.55          | (v4_pre_topc @ (sk_D @ X14 @ X12 @ X13) @ X13)
% 0.25/0.55          | ~ (r1_tarski @ X14 @ X12)
% 0.25/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (l1_pre_topc @ X13))),
% 0.25/0.55      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.25/0.55  thf('27', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (l1_pre_topc @ sk_A)
% 0.25/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.25/0.55          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.25/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.25/0.55  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('29', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('30', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.25/0.55          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.25/0.55      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.25/0.55  thf('31', plain,
% 0.25/0.55      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.25/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['24', '30'])).
% 0.25/0.55  thf('32', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.25/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.55  thf('33', plain,
% 0.25/0.55      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.25/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.25/0.55  thf('34', plain,
% 0.25/0.55      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.25/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('sup+', [status(thm)], ['4', '11'])).
% 0.25/0.55  thf('35', plain,
% 0.25/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('36', plain,
% 0.25/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (v2_tex_2 @ X12 @ X13)
% 0.25/0.55          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ 
% 0.25/0.55              (sk_D @ X14 @ X12 @ X13)) = (X14))
% 0.25/0.55          | ~ (r1_tarski @ X14 @ X12)
% 0.25/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.25/0.55          | ~ (l1_pre_topc @ X13))),
% 0.25/0.55      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.25/0.55  thf('37', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (l1_pre_topc @ sk_A)
% 0.25/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.25/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.25/0.55              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.25/0.55          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.25/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.25/0.55  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.25/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.55  thf('40', plain,
% 0.25/0.55      (![X0 : $i]:
% 0.25/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.25/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.25/0.55          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.25/0.55              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.25/0.55      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.25/0.55  thf('41', plain,
% 0.25/0.55      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.25/0.55          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.25/0.55        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.25/0.55      inference('sup-', [status(thm)], ['34', '40'])).
% 0.25/0.55  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.25/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.25/0.55  thf('43', plain,
% 0.25/0.55      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.25/0.55         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.25/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.25/0.55  thf('44', plain, (((k1_tarski @ sk_C_1) != (k1_tarski @ sk_C_1))),
% 0.25/0.55      inference('demod', [status(thm)], ['23', '33', '43'])).
% 0.25/0.55  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.25/0.55  
% 0.25/0.55  % SZS output end Refutation
% 0.25/0.55  
% 0.25/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

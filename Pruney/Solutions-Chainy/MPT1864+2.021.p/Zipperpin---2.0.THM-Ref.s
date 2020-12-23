%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cc96cI5qnw

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 145 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  579 (2247 expanded)
%              Number of equality atoms :   13 (  61 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t32_tex_2,conjecture,(
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
                       => ~ ( ( v3_pre_topc @ D @ A )
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
                         => ~ ( ( v3_pre_topc @ D @ A )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X8 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X14: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X14 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X14 @ sk_A )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 @ ( sk_D @ X12 @ X10 @ X11 ) )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
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
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('33',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k1_tarski @ sk_C_1 )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['23','33'])).

thf('35',plain,(
    ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v2_tex_2 @ X10 @ X11 )
      | ( v3_pre_topc @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('45',plain,(
    v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['35','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cc96cI5qnw
% 0.12/0.35  % Computer   : n006.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 14:47:53 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 53 iterations in 0.037s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(t32_tex_2, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.50             ( ![C:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.50                      ( ![D:$i]:
% 0.21/0.50                        ( ( m1_subset_1 @
% 0.21/0.50                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.50                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.50                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( l1_pre_topc @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50              ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.50                ( ![C:$i]:
% 0.21/0.50                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.50                         ( ![D:$i]:
% 0.21/0.50                           ( ( m1_subset_1 @
% 0.21/0.50                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.50                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.50                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.21/0.50  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(l3_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X5 @ X6)
% 0.21/0.50          | (r2_hidden @ X5 @ X7)
% 0.21/0.50          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.50  thf(t63_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k1_tarski @ X8) @ (k1_zfmisc_1 @ X9))
% 0.21/0.50          | ~ (r2_hidden @ X8 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d5_tex_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.50             ( ![C:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.50                      ( ![D:$i]:
% 0.21/0.50                        ( ( m1_subset_1 @
% 0.21/0.50                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.50                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.50                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (v2_tex_2 @ X10 @ X11)
% 0.21/0.50          | (m1_subset_1 @ (sk_D @ X12 @ X10 @ X11) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (r1_tarski @ X12 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (l1_pre_topc @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.50          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.21/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '12'])).
% 0.21/0.50  thf('14', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t38_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         ((r1_tarski @ (k2_tarski @ X1 @ X3) @ X4)
% 0.21/0.50          | ~ (r2_hidden @ X3 @ X4)
% 0.21/0.50          | ~ (r2_hidden @ X1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.50          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.50  thf(t69_enumset1, axiom,
% 0.21/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.50  thf('19', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.50  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['13', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X14 : $i]:
% 0.21/0.50         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X14)
% 0.21/0.50            != (k1_tarski @ sk_C_1))
% 0.21/0.50          | ~ (v3_pre_topc @ X14 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.21/0.50            != (k1_tarski @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (v2_tex_2 @ X10 @ X11)
% 0.21/0.50          | ((k9_subset_1 @ (u1_struct_0 @ X11) @ X10 @ 
% 0.21/0.50              (sk_D @ X12 @ X10 @ X11)) = (X12))
% 0.21/0.50          | ~ (r1_tarski @ X12 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (l1_pre_topc @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.50          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.21/0.50          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.50          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.21/0.50        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['24', '30'])).
% 0.21/0.50  thf('32', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.50         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      ((~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50        | ((k1_tarski @ sk_C_1) != (k1_tarski @ sk_C_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['23', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (v2_tex_2 @ X10 @ X11)
% 0.21/0.50          | (v3_pre_topc @ (sk_D @ X12 @ X10 @ X11) @ X11)
% 0.21/0.50          | ~ (r1_tarski @ X12 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.21/0.50          | ~ (l1_pre_topc @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.50          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.50          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '42'])).
% 0.21/0.50  thf('44', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ($false), inference('demod', [status(thm)], ['35', '45'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

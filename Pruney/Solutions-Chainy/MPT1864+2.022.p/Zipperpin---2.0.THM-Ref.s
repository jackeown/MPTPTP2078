%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ukkhbtSING

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 131 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  542 (1990 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X15: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X15 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X15 @ sk_A )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( v3_pre_topc @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,(
    v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v2_tex_2 @ X11 @ X12 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ ( sk_D @ X13 @ X11 @ X12 ) )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('41',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ( k1_tarski @ sk_C_1 )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','31','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ukkhbtSING
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:33:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 62 iterations in 0.041s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(t32_tex_2, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.51             ( ![C:$i]:
% 0.22/0.51               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.51                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.22/0.51                      ( ![D:$i]:
% 0.22/0.51                        ( ( m1_subset_1 @
% 0.22/0.51                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.51                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.22/0.51                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( l1_pre_topc @ A ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51              ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.51                ( ![C:$i]:
% 0.22/0.51                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.51                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.22/0.51                         ( ![D:$i]:
% 0.22/0.51                           ( ( m1_subset_1 @
% 0.22/0.51                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.51                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.22/0.51                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.22/0.51  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(l3_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.51          | (r2_hidden @ X3 @ X5)
% 0.22/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain, ((r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.51  thf(t63_subset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.22/0.51          | ~ (r2_hidden @ X6 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d5_tex_2, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51           ( ( v2_tex_2 @ B @ A ) <=>
% 0.22/0.51             ( ![C:$i]:
% 0.22/0.51               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.22/0.51                      ( ![D:$i]:
% 0.22/0.51                        ( ( m1_subset_1 @
% 0.22/0.51                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.51                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.51                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.22/0.51                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | ~ (v2_tex_2 @ X11 @ X12)
% 0.22/0.51          | (m1_subset_1 @ (sk_D @ X13 @ X11 @ X12) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | ~ (r1_tarski @ X13 @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | ~ (l1_pre_topc @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('11', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.22/0.51         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '12'])).
% 0.22/0.51  thf('14', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.22/0.51          | ~ (r2_hidden @ X6 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf(t3_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('18', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('demod', [status(thm)], ['13', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X15 : $i]:
% 0.22/0.51         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X15)
% 0.22/0.51            != (k1_tarski @ sk_C_1))
% 0.22/0.51          | ~ (v3_pre_topc @ X15 @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      ((~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.22/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.22/0.51            != (k1_tarski @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | ~ (v2_tex_2 @ X11 @ X12)
% 0.22/0.51          | (v3_pre_topc @ (sk_D @ X13 @ X11 @ X12) @ X12)
% 0.22/0.51          | ~ (r1_tarski @ X13 @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | ~ (l1_pre_topc @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.22/0.51          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.51  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.22/0.51        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '28'])).
% 0.22/0.51  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.22/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | ~ (v2_tex_2 @ X11 @ X12)
% 0.22/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X12) @ X11 @ 
% 0.22/0.51              (sk_D @ X13 @ X11 @ X12)) = (X13))
% 0.22/0.51          | ~ (r1_tarski @ X13 @ X11)
% 0.22/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.51          | ~ (l1_pre_topc @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.22/0.51          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.51  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('37', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.22/0.51        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['32', '38'])).
% 0.22/0.51  thf('40', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.51  thf('42', plain, (((k1_tarski @ sk_C_1) != (k1_tarski @ sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['21', '31', '41'])).
% 0.22/0.51  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

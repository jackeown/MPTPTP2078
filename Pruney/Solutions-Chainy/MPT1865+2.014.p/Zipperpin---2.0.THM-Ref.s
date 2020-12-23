%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eH2vlmHbvD

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:22 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 140 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  555 (2033 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ ( sk_D @ X14 @ X12 @ X13 ) )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X16: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X16 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v4_pre_topc @ X16 @ sk_A )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v4_pre_topc @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
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
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('43',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['33','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eH2vlmHbvD
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:22:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 190 iterations in 0.148s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.59  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.42/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.59  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.42/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.42/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.59  thf(t33_tex_2, conjecture,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( v2_tex_2 @ B @ A ) =>
% 0.42/0.59             ( ![C:$i]:
% 0.42/0.59               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.42/0.59                      ( ![D:$i]:
% 0.42/0.59                        ( ( m1_subset_1 @
% 0.42/0.59                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.42/0.59                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.42/0.59                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i]:
% 0.42/0.59        ( ( l1_pre_topc @ A ) =>
% 0.42/0.59          ( ![B:$i]:
% 0.42/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59              ( ( v2_tex_2 @ B @ A ) =>
% 0.42/0.59                ( ![C:$i]:
% 0.42/0.59                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.42/0.59                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.42/0.59                         ( ![D:$i]:
% 0.42/0.59                           ( ( m1_subset_1 @
% 0.42/0.59                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.42/0.59                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.42/0.59                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.42/0.59  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(t3_subset, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      (![X9 : $i, X10 : $i]:
% 0.42/0.59         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.59  thf(d3_tarski, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (~ (r2_hidden @ X0 @ X1)
% 0.42/0.59          | (r2_hidden @ X0 @ X2)
% 0.42/0.59          | ~ (r1_tarski @ X1 @ X2))),
% 0.42/0.59      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.59  thf('6', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['0', '5'])).
% 0.42/0.59  thf(t37_zfmisc_1, axiom,
% 0.42/0.59    (![A:$i,B:$i]:
% 0.42/0.59     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.42/0.59  thf('7', plain,
% 0.42/0.59      (![X4 : $i, X6 : $i]:
% 0.42/0.59         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.42/0.59      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.42/0.59  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.59  thf('9', plain,
% 0.42/0.59      (![X9 : $i, X11 : $i]:
% 0.42/0.59         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.42/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(d6_tex_2, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( l1_pre_topc @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59           ( ( v2_tex_2 @ B @ A ) <=>
% 0.42/0.59             ( ![C:$i]:
% 0.42/0.59               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.42/0.59                      ( ![D:$i]:
% 0.42/0.59                        ( ( m1_subset_1 @
% 0.42/0.59                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.59                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.42/0.59                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.42/0.59                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.42/0.59          | ~ (v2_tex_2 @ X12 @ X13)
% 0.42/0.59          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ 
% 0.42/0.59              (sk_D @ X14 @ X12 @ X13)) = (X14))
% 0.42/0.59          | ~ (r1_tarski @ X14 @ X12)
% 0.42/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.42/0.59          | ~ (l1_pre_topc @ X13))),
% 0.42/0.59      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.42/0.59  thf('13', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (l1_pre_topc @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.59          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.42/0.59          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.59  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.59          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.42/0.59      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59          (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 0.42/0.59        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '16'])).
% 0.42/0.59  thf('18', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('19', plain,
% 0.42/0.59      (![X4 : $i, X6 : $i]:
% 0.42/0.59         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.42/0.59      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.42/0.59  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.42/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.59  thf('21', plain,
% 0.42/0.59      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))),
% 0.42/0.59      inference('demod', [status(thm)], ['17', '20'])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf('23', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('24', plain,
% 0.42/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.42/0.59          | ~ (v2_tex_2 @ X12 @ X13)
% 0.42/0.59          | (m1_subset_1 @ (sk_D @ X14 @ X12 @ X13) @ 
% 0.42/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.42/0.59          | ~ (r1_tarski @ X14 @ X12)
% 0.42/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.42/0.59          | ~ (l1_pre_topc @ X13))),
% 0.42/0.59      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.42/0.59  thf('25', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (l1_pre_topc @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.59          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.42/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.59  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('28', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.59          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.42/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.59      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.42/0.59  thf('29', plain,
% 0.42/0.59      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.42/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['22', '28'])).
% 0.42/0.59  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.42/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.59  thf('31', plain,
% 0.42/0.59      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.42/0.59  thf('32', plain,
% 0.42/0.59      (![X16 : $i]:
% 0.42/0.59         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X16)
% 0.42/0.59            != (k1_tarski @ sk_C_2))
% 0.42/0.59          | ~ (v4_pre_topc @ X16 @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('33', plain,
% 0.42/0.59      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.42/0.59        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 0.42/0.59            != (k1_tarski @ sk_C_2)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.59  thf('34', plain,
% 0.42/0.59      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf('35', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('36', plain,
% 0.42/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.42/0.59          | ~ (v2_tex_2 @ X12 @ X13)
% 0.42/0.59          | (v4_pre_topc @ (sk_D @ X14 @ X12 @ X13) @ X13)
% 0.42/0.59          | ~ (r1_tarski @ X14 @ X12)
% 0.42/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.42/0.59          | ~ (l1_pre_topc @ X13))),
% 0.42/0.59      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.42/0.59  thf('37', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (l1_pre_topc @ sk_A)
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.59          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.42/0.59          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.59  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('40', plain,
% 0.42/0.59      (![X0 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.59          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.59          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.42/0.59      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.42/0.59  thf('41', plain,
% 0.42/0.59      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.42/0.59        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.42/0.59      inference('sup-', [status(thm)], ['34', '40'])).
% 0.42/0.59  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.42/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.59  thf('43', plain,
% 0.42/0.59      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)),
% 0.42/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.42/0.59  thf('44', plain,
% 0.42/0.59      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.42/0.59         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_2))),
% 0.42/0.59      inference('demod', [status(thm)], ['33', '43'])).
% 0.42/0.59  thf('45', plain, ($false),
% 0.42/0.59      inference('simplify_reflect-', [status(thm)], ['21', '44'])).
% 0.42/0.59  
% 0.42/0.59  % SZS output end Refutation
% 0.42/0.59  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ms5gPzYZae

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:17 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 140 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  555 (2033 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ ( sk_D @ X15 @ X13 @ X14 ) )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

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
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

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
    ! [X17: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X17 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v3_pre_topc @ X17 @ sk_A )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v3_pre_topc @ ( sk_D @ X15 @ X13 @ X14 ) @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
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
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('43',plain,(
    v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ms5gPzYZae
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 194 iterations in 0.159s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.63  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.44/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.63  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.44/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(t32_tex_2, conjecture,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_pre_topc @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( ( v2_tex_2 @ B @ A ) =>
% 0.44/0.63             ( ![C:$i]:
% 0.44/0.63               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.44/0.63                      ( ![D:$i]:
% 0.44/0.63                        ( ( m1_subset_1 @
% 0.44/0.63                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.44/0.63                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.44/0.63                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i]:
% 0.44/0.63        ( ( l1_pre_topc @ A ) =>
% 0.44/0.63          ( ![B:$i]:
% 0.44/0.63            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63              ( ( v2_tex_2 @ B @ A ) =>
% 0.44/0.63                ( ![C:$i]:
% 0.44/0.63                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.63                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.44/0.63                         ( ![D:$i]:
% 0.44/0.63                           ( ( m1_subset_1 @
% 0.44/0.63                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.44/0.63                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.44/0.63                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.44/0.63  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(t3_subset, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (![X10 : $i, X11 : $i]:
% 0.44/0.63         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.44/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.63  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.63  thf(d3_tarski, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.63  thf('4', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.63          | (r2_hidden @ X0 @ X2)
% 0.44/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.63  thf('5', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.63  thf('6', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['0', '5'])).
% 0.44/0.63  thf(l1_zfmisc_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (![X7 : $i, X9 : $i]:
% 0.44/0.63         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.44/0.63  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (![X10 : $i, X12 : $i]:
% 0.44/0.63         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.44/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.63  thf('10', plain,
% 0.44/0.63      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(d5_tex_2, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( l1_pre_topc @ A ) =>
% 0.44/0.63       ( ![B:$i]:
% 0.44/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63           ( ( v2_tex_2 @ B @ A ) <=>
% 0.44/0.63             ( ![C:$i]:
% 0.44/0.63               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.44/0.63                      ( ![D:$i]:
% 0.44/0.63                        ( ( m1_subset_1 @
% 0.44/0.63                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.63                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.44/0.63                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.44/0.63                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (v2_tex_2 @ X13 @ X14)
% 0.44/0.63          | ((k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ 
% 0.44/0.63              (sk_D @ X15 @ X13 @ X14)) = (X15))
% 0.44/0.63          | ~ (r1_tarski @ X15 @ X13)
% 0.44/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (l1_pre_topc @ X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (l1_pre_topc @ sk_A)
% 0.44/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_tarski @ X0 @ sk_B)
% 0.44/0.63          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.44/0.63          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.63  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('16', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_tarski @ X0 @ sk_B)
% 0.44/0.63          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.44/0.63      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.44/0.63  thf('17', plain,
% 0.44/0.63      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63          (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 0.44/0.63        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['10', '16'])).
% 0.44/0.63  thf('18', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      (![X7 : $i, X9 : $i]:
% 0.44/0.63         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.44/0.63      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.44/0.63  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.44/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))),
% 0.44/0.63      inference('demod', [status(thm)], ['17', '20'])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('23', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('24', plain,
% 0.44/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (v2_tex_2 @ X13 @ X14)
% 0.44/0.63          | (m1_subset_1 @ (sk_D @ X15 @ X13 @ X14) @ 
% 0.44/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (r1_tarski @ X15 @ X13)
% 0.44/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (l1_pre_topc @ X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (l1_pre_topc @ sk_A)
% 0.44/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_tarski @ X0 @ sk_B)
% 0.44/0.63          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.44/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.63  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_tarski @ X0 @ sk_B)
% 0.44/0.63          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.44/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.44/0.63         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['22', '28'])).
% 0.44/0.63  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.44/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.63  thf('31', plain,
% 0.44/0.63      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.44/0.63  thf('32', plain,
% 0.44/0.63      (![X17 : $i]:
% 0.44/0.63         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X17)
% 0.44/0.63            != (k1_tarski @ sk_C_2))
% 0.44/0.63          | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.44/0.63          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('33', plain,
% 0.44/0.63      ((~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.44/0.63        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 0.44/0.63            != (k1_tarski @ sk_C_2)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.63  thf('34', plain,
% 0.44/0.63      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.44/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('35', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('36', plain,
% 0.44/0.63      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (v2_tex_2 @ X13 @ X14)
% 0.44/0.63          | (v3_pre_topc @ (sk_D @ X15 @ X13 @ X14) @ X14)
% 0.44/0.63          | ~ (r1_tarski @ X15 @ X13)
% 0.44/0.63          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.44/0.63          | ~ (l1_pre_topc @ X14))),
% 0.44/0.63      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.44/0.63  thf('37', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (l1_pre_topc @ sk_A)
% 0.44/0.63          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_tarski @ X0 @ sk_B)
% 0.44/0.63          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.44/0.63          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.44/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.63  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('40', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.63          | ~ (r1_tarski @ X0 @ sk_B)
% 0.44/0.63          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.44/0.63      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.44/0.63  thf('41', plain,
% 0.44/0.63      (((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.44/0.63        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['34', '40'])).
% 0.44/0.63  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.44/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.63  thf('43', plain,
% 0.44/0.63      ((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)),
% 0.44/0.63      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.63  thf('44', plain,
% 0.44/0.63      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.44/0.63         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_2))),
% 0.44/0.63      inference('demod', [status(thm)], ['33', '43'])).
% 0.44/0.63  thf('45', plain, ($false),
% 0.44/0.63      inference('simplify_reflect-', [status(thm)], ['21', '44'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

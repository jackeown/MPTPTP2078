%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AM64zA2NoF

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:20 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 140 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  548 (2026 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
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
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_tex_2 @ X38 @ X39 )
      | ( m1_subset_1 @ ( sk_D_1 @ X40 @ X38 @ X39 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( r1_tarski @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X42: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X42 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v4_pre_topc @ X42 @ sk_A )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( v4_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_tex_2 @ X38 @ X39 )
      | ( v4_pre_topc @ ( sk_D_1 @ X40 @ X38 @ X39 ) @ X39 )
      | ~ ( r1_tarski @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A )
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
      | ( v4_pre_topc @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( v4_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('33',plain,(
    v4_pre_topc @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( v2_tex_2 @ X38 @ X39 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 @ ( sk_D_1 @ X40 @ X38 @ X39 ) )
        = X40 )
      | ~ ( r1_tarski @ X40 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
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
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('43',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_tarski @ sk_C_2 )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['23','33','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AM64zA2NoF
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.18/1.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.18/1.36  % Solved by: fo/fo7.sh
% 1.18/1.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.36  % done 2349 iterations in 0.908s
% 1.18/1.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.18/1.36  % SZS output start Refutation
% 1.18/1.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.18/1.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.36  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.18/1.36  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.18/1.36  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.18/1.36  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 1.18/1.36  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.18/1.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.18/1.36  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.18/1.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.18/1.36  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.36  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.36  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.18/1.36  thf(t33_tex_2, conjecture,
% 1.18/1.36    (![A:$i]:
% 1.18/1.36     ( ( l1_pre_topc @ A ) =>
% 1.18/1.36       ( ![B:$i]:
% 1.18/1.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.36           ( ( v2_tex_2 @ B @ A ) =>
% 1.18/1.36             ( ![C:$i]:
% 1.18/1.36               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.36                 ( ~( ( r2_hidden @ C @ B ) & 
% 1.18/1.36                      ( ![D:$i]:
% 1.18/1.36                        ( ( m1_subset_1 @
% 1.18/1.36                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.36                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.18/1.36                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.18/1.36                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.36  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.36    (~( ![A:$i]:
% 1.18/1.36        ( ( l1_pre_topc @ A ) =>
% 1.18/1.36          ( ![B:$i]:
% 1.18/1.36            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.36              ( ( v2_tex_2 @ B @ A ) =>
% 1.18/1.36                ( ![C:$i]:
% 1.18/1.36                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.18/1.36                    ( ~( ( r2_hidden @ C @ B ) & 
% 1.18/1.36                         ( ![D:$i]:
% 1.18/1.36                           ( ( m1_subset_1 @
% 1.18/1.36                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.36                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.18/1.36                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.18/1.36                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.18/1.36    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 1.18/1.36  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('1', plain,
% 1.18/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf(t3_subset, axiom,
% 1.18/1.36    (![A:$i,B:$i]:
% 1.18/1.36     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.18/1.36  thf('2', plain,
% 1.18/1.36      (![X30 : $i, X31 : $i]:
% 1.18/1.36         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 1.18/1.36      inference('cnf', [status(esa)], [t3_subset])).
% 1.18/1.36  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.18/1.36      inference('sup-', [status(thm)], ['1', '2'])).
% 1.18/1.36  thf(d3_tarski, axiom,
% 1.18/1.36    (![A:$i,B:$i]:
% 1.18/1.36     ( ( r1_tarski @ A @ B ) <=>
% 1.18/1.36       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.18/1.36  thf('4', plain,
% 1.18/1.36      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.18/1.36         (~ (r2_hidden @ X2 @ X3)
% 1.18/1.36          | (r2_hidden @ X2 @ X4)
% 1.18/1.36          | ~ (r1_tarski @ X3 @ X4))),
% 1.18/1.36      inference('cnf', [status(esa)], [d3_tarski])).
% 1.18/1.36  thf('5', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.18/1.36      inference('sup-', [status(thm)], ['3', '4'])).
% 1.18/1.36  thf('6', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 1.18/1.36      inference('sup-', [status(thm)], ['0', '5'])).
% 1.18/1.36  thf(l1_zfmisc_1, axiom,
% 1.18/1.36    (![A:$i,B:$i]:
% 1.18/1.36     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.18/1.36  thf('7', plain,
% 1.18/1.36      (![X16 : $i, X18 : $i]:
% 1.18/1.36         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 1.18/1.36      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.18/1.36  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 1.18/1.36      inference('sup-', [status(thm)], ['6', '7'])).
% 1.18/1.36  thf('9', plain,
% 1.18/1.36      (![X30 : $i, X32 : $i]:
% 1.18/1.36         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 1.18/1.36      inference('cnf', [status(esa)], [t3_subset])).
% 1.18/1.36  thf('10', plain,
% 1.18/1.36      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 1.18/1.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.18/1.36  thf('11', plain,
% 1.18/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf(d6_tex_2, axiom,
% 1.18/1.36    (![A:$i]:
% 1.18/1.36     ( ( l1_pre_topc @ A ) =>
% 1.18/1.36       ( ![B:$i]:
% 1.18/1.36         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.36           ( ( v2_tex_2 @ B @ A ) <=>
% 1.18/1.36             ( ![C:$i]:
% 1.18/1.36               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.36                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.18/1.36                      ( ![D:$i]:
% 1.18/1.36                        ( ( m1_subset_1 @
% 1.18/1.36                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.18/1.36                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.18/1.36                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.18/1.36                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.18/1.36  thf('12', plain,
% 1.18/1.36      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.18/1.36         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.18/1.36          | ~ (v2_tex_2 @ X38 @ X39)
% 1.18/1.36          | (m1_subset_1 @ (sk_D_1 @ X40 @ X38 @ X39) @ 
% 1.18/1.36             (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.18/1.36          | ~ (r1_tarski @ X40 @ X38)
% 1.18/1.36          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.18/1.36          | ~ (l1_pre_topc @ X39))),
% 1.18/1.36      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.18/1.36  thf('13', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         (~ (l1_pre_topc @ sk_A)
% 1.18/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36          | ~ (r1_tarski @ X0 @ sk_B)
% 1.18/1.36          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 1.18/1.36             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.18/1.36      inference('sup-', [status(thm)], ['11', '12'])).
% 1.18/1.36  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('16', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36          | ~ (r1_tarski @ X0 @ sk_B)
% 1.18/1.36          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 1.18/1.36             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.36      inference('demod', [status(thm)], ['13', '14', '15'])).
% 1.18/1.36  thf('17', plain,
% 1.18/1.36      (((m1_subset_1 @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 1.18/1.36         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 1.18/1.36      inference('sup-', [status(thm)], ['10', '16'])).
% 1.18/1.36  thf('18', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('19', plain,
% 1.18/1.36      (![X16 : $i, X18 : $i]:
% 1.18/1.36         ((r1_tarski @ (k1_tarski @ X16) @ X18) | ~ (r2_hidden @ X16 @ X18))),
% 1.18/1.36      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.18/1.36  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 1.18/1.36      inference('sup-', [status(thm)], ['18', '19'])).
% 1.18/1.36  thf('21', plain,
% 1.18/1.36      ((m1_subset_1 @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 1.18/1.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('demod', [status(thm)], ['17', '20'])).
% 1.18/1.36  thf('22', plain,
% 1.18/1.36      (![X42 : $i]:
% 1.18/1.36         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X42)
% 1.18/1.36            != (k1_tarski @ sk_C_2))
% 1.18/1.36          | ~ (v4_pre_topc @ X42 @ sk_A)
% 1.18/1.36          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('23', plain,
% 1.18/1.36      ((~ (v4_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 1.18/1.36        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.36            (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 1.18/1.36            != (k1_tarski @ sk_C_2)))),
% 1.18/1.36      inference('sup-', [status(thm)], ['21', '22'])).
% 1.18/1.36  thf('24', plain,
% 1.18/1.36      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 1.18/1.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.18/1.36  thf('25', plain,
% 1.18/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('26', plain,
% 1.18/1.36      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.18/1.36         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.18/1.36          | ~ (v2_tex_2 @ X38 @ X39)
% 1.18/1.36          | (v4_pre_topc @ (sk_D_1 @ X40 @ X38 @ X39) @ X39)
% 1.18/1.36          | ~ (r1_tarski @ X40 @ X38)
% 1.18/1.36          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.18/1.36          | ~ (l1_pre_topc @ X39))),
% 1.18/1.36      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.18/1.36  thf('27', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         (~ (l1_pre_topc @ sk_A)
% 1.18/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36          | ~ (r1_tarski @ X0 @ sk_B)
% 1.18/1.36          | (v4_pre_topc @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A)
% 1.18/1.36          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.18/1.36      inference('sup-', [status(thm)], ['25', '26'])).
% 1.18/1.36  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('29', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('30', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36          | ~ (r1_tarski @ X0 @ sk_B)
% 1.18/1.36          | (v4_pre_topc @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ sk_A))),
% 1.18/1.36      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.18/1.36  thf('31', plain,
% 1.18/1.36      (((v4_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 1.18/1.36        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 1.18/1.36      inference('sup-', [status(thm)], ['24', '30'])).
% 1.18/1.36  thf('32', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 1.18/1.36      inference('sup-', [status(thm)], ['18', '19'])).
% 1.18/1.36  thf('33', plain,
% 1.18/1.36      ((v4_pre_topc @ (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)),
% 1.18/1.36      inference('demod', [status(thm)], ['31', '32'])).
% 1.18/1.36  thf('34', plain,
% 1.18/1.36      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 1.18/1.36        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('sup-', [status(thm)], ['8', '9'])).
% 1.18/1.36  thf('35', plain,
% 1.18/1.36      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('36', plain,
% 1.18/1.36      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.18/1.36         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.18/1.36          | ~ (v2_tex_2 @ X38 @ X39)
% 1.18/1.36          | ((k9_subset_1 @ (u1_struct_0 @ X39) @ X38 @ 
% 1.18/1.36              (sk_D_1 @ X40 @ X38 @ X39)) = (X40))
% 1.18/1.36          | ~ (r1_tarski @ X40 @ X38)
% 1.18/1.36          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.18/1.36          | ~ (l1_pre_topc @ X39))),
% 1.18/1.36      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.18/1.36  thf('37', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         (~ (l1_pre_topc @ sk_A)
% 1.18/1.36          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36          | ~ (r1_tarski @ X0 @ sk_B)
% 1.18/1.36          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.36              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (X0))
% 1.18/1.36          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.18/1.36      inference('sup-', [status(thm)], ['35', '36'])).
% 1.18/1.36  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.18/1.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.36  thf('40', plain,
% 1.18/1.36      (![X0 : $i]:
% 1.18/1.36         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.18/1.36          | ~ (r1_tarski @ X0 @ sk_B)
% 1.18/1.36          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.36              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (X0)))),
% 1.18/1.36      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.18/1.36  thf('41', plain,
% 1.18/1.36      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.36          (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 1.18/1.36        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 1.18/1.36      inference('sup-', [status(thm)], ['34', '40'])).
% 1.18/1.36  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 1.18/1.36      inference('sup-', [status(thm)], ['18', '19'])).
% 1.18/1.36  thf('43', plain,
% 1.18/1.36      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.18/1.36         (sk_D_1 @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))),
% 1.18/1.36      inference('demod', [status(thm)], ['41', '42'])).
% 1.18/1.36  thf('44', plain, (((k1_tarski @ sk_C_2) != (k1_tarski @ sk_C_2))),
% 1.18/1.36      inference('demod', [status(thm)], ['23', '33', '43'])).
% 1.18/1.36  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 1.18/1.36  
% 1.18/1.36  % SZS output end Refutation
% 1.18/1.36  
% 1.18/1.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

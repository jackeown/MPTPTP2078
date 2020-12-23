%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J60mD5EoxW

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:16 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 140 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  555 (2033 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
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
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ ( sk_D @ X25 @ X23 @ X24 ) )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ X16 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ( m1_subset_1 @ ( sk_D @ X25 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X27: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X27 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v2_tex_2 @ X23 @ X24 )
      | ( v3_pre_topc @ ( sk_D @ X25 @ X23 @ X24 ) @ X24 )
      | ~ ( r1_tarski @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.J60mD5EoxW
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 1314 iterations in 0.501s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.76/0.96  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.76/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.76/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.96  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.76/0.96  thf(t32_tex_2, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( v2_tex_2 @ B @ A ) =>
% 0.76/0.96             ( ![C:$i]:
% 0.76/0.96               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.76/0.96                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.76/0.96                      ( ![D:$i]:
% 0.76/0.96                        ( ( m1_subset_1 @
% 0.76/0.96                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.76/0.96                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.76/0.96                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( l1_pre_topc @ A ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96              ( ( v2_tex_2 @ B @ A ) =>
% 0.76/0.96                ( ![C:$i]:
% 0.76/0.96                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.76/0.96                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.76/0.96                         ( ![D:$i]:
% 0.76/0.96                           ( ( m1_subset_1 @
% 0.76/0.96                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.76/0.96                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.76/0.96                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.76/0.96  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(t3_subset, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      (![X20 : $i, X21 : $i]:
% 0.76/0.96         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf(d3_tarski, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.96       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.96  thf('4', plain,
% 0.76/0.96      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.76/0.96         (~ (r2_hidden @ X2 @ X3)
% 0.76/0.96          | (r2_hidden @ X2 @ X4)
% 0.76/0.96          | ~ (r1_tarski @ X3 @ X4))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['3', '4'])).
% 0.76/0.96  thf('6', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['0', '5'])).
% 0.76/0.96  thf(l1_zfmisc_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (![X14 : $i, X16 : $i]:
% 0.76/0.96         ((r1_tarski @ (k1_tarski @ X14) @ X16) | ~ (r2_hidden @ X14 @ X16))),
% 0.76/0.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.76/0.96  thf('8', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (![X20 : $i, X22 : $i]:
% 0.76/0.96         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 0.76/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(d5_tex_2, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_pre_topc @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96           ( ( v2_tex_2 @ B @ A ) <=>
% 0.76/0.96             ( ![C:$i]:
% 0.76/0.96               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.76/0.96                      ( ![D:$i]:
% 0.76/0.96                        ( ( m1_subset_1 @
% 0.76/0.96                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.96                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.76/0.96                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.76/0.96                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf('12', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.96          | ~ (v2_tex_2 @ X23 @ X24)
% 0.76/0.96          | ((k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ 
% 0.76/0.96              (sk_D @ X25 @ X23 @ X24)) = (X25))
% 0.76/0.96          | ~ (r1_tarski @ X25 @ X23)
% 0.76/0.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.96          | ~ (l1_pre_topc @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.76/0.96          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.96  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.76/0.96      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96          (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 0.76/0.96        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['10', '16'])).
% 0.76/0.96  thf('18', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('19', plain,
% 0.76/0.96      (![X14 : $i, X16 : $i]:
% 0.76/0.96         ((r1_tarski @ (k1_tarski @ X14) @ X16) | ~ (r2_hidden @ X14 @ X16))),
% 0.76/0.96      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.76/0.96  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.76/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.96  thf('21', plain,
% 0.76/0.96      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))),
% 0.76/0.96      inference('demod', [status(thm)], ['17', '20'])).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('24', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.96          | ~ (v2_tex_2 @ X23 @ X24)
% 0.76/0.96          | (m1_subset_1 @ (sk_D @ X25 @ X23 @ X24) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.96          | ~ (r1_tarski @ X25 @ X23)
% 0.76/0.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.96          | ~ (l1_pre_topc @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.96  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('28', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.76/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['22', '28'])).
% 0.76/0.96  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.76/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.96  thf('31', plain,
% 0.76/0.96      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (![X27 : $i]:
% 0.76/0.96         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X27)
% 0.76/0.96            != (k1_tarski @ sk_C_2))
% 0.76/0.96          | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('33', plain,
% 0.76/0.96      ((~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.76/0.96        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 0.76/0.96            != (k1_tarski @ sk_C_2)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.76/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['8', '9'])).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.96          | ~ (v2_tex_2 @ X23 @ X24)
% 0.76/0.96          | (v3_pre_topc @ (sk_D @ X25 @ X23 @ X24) @ X24)
% 0.76/0.96          | ~ (r1_tarski @ X25 @ X23)
% 0.76/0.96          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.76/0.96          | ~ (l1_pre_topc @ X24))),
% 0.76/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (l1_pre_topc @ sk_A)
% 0.76/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.76/0.96          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.96  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.76/0.96          | ~ (r1_tarski @ X0 @ sk_B)
% 0.76/0.96          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      (((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.76/0.96        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['34', '40'])).
% 0.76/0.96  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.76/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      ((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)),
% 0.76/0.96      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf('44', plain,
% 0.76/0.96      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.76/0.96         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_2))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '43'])).
% 0.76/0.96  thf('45', plain, ($false),
% 0.76/0.96      inference('simplify_reflect-', [status(thm)], ['21', '44'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6XY6XHxYtD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 213 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  621 (3008 expanded)
%              Number of equality atoms :   14 (  79 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf('7',plain,(
    r2_hidden @ sk_C_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X5 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_2 @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('12',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ ( sk_D @ X14 @ X12 @ X13 ) )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X5 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_2 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('39',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X16 )
       != ( k1_tarski @ sk_C_2 ) )
      | ~ ( v4_pre_topc @ X16 @ sk_A )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( v4_pre_topc @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('51',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6XY6XHxYtD
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 201 iterations in 0.119s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(t33_tex_2, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.57             ( ![C:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.57                      ( ![D:$i]:
% 0.21/0.57                        ( ( m1_subset_1 @
% 0.21/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.57                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.57                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( l1_pre_topc @ A ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57              ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.57                ( ![C:$i]:
% 0.21/0.57                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.57                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.57                         ( ![D:$i]:
% 0.21/0.57                           ( ( m1_subset_1 @
% 0.21/0.57                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.57                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.57                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.21/0.57  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t3_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.57          | (r2_hidden @ X0 @ X2)
% 0.21/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.57  thf('7', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.21/0.57  thf(t38_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         ((r1_tarski @ (k2_tarski @ X5 @ X7) @ X8)
% 0.21/0.57          | ~ (r2_hidden @ X7 @ X8)
% 0.21/0.57          | ~ (r2_hidden @ X5 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.57          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      ((r1_tarski @ (k2_tarski @ sk_C_2 @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.57  thf(t69_enumset1, axiom,
% 0.21/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.57  thf('11', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.57  thf('12', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ (u1_struct_0 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X9 : $i, X11 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d6_tex_2, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.57             ( ![C:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.57                      ( ![D:$i]:
% 0.21/0.57                        ( ( m1_subset_1 @
% 0.21/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.21/0.57                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.57                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (v2_tex_2 @ X12 @ X13)
% 0.21/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ 
% 0.21/0.57              (sk_D @ X14 @ X12 @ X13)) = (X14))
% 0.21/0.57          | ~ (r1_tarski @ X14 @ X12)
% 0.21/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (l1_pre_topc @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.57              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.21/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.57  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('19', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.57              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.57          (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 0.21/0.57        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '20'])).
% 0.21/0.57  thf('22', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('23', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         ((r1_tarski @ (k2_tarski @ X5 @ X7) @ X8)
% 0.21/0.57          | ~ (r2_hidden @ X7 @ X8)
% 0.21/0.57          | ~ (r2_hidden @ X5 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.57          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_2) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.57  thf('26', plain, ((r1_tarski @ (k2_tarski @ sk_C_2 @ sk_C_2) @ sk_B)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '25'])).
% 0.21/0.57  thf('27', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.57  thf('28', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.57         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))),
% 0.21/0.57      inference('demod', [status(thm)], ['21', '28'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (v2_tex_2 @ X12 @ X13)
% 0.21/0.57          | (m1_subset_1 @ (sk_D @ X14 @ X12 @ X13) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (r1_tarski @ X14 @ X12)
% 0.21/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (l1_pre_topc @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.57  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('35', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.21/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '36'])).
% 0.21/0.57  thf('38', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X16 : $i]:
% 0.21/0.57         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X16)
% 0.21/0.57            != (k1_tarski @ sk_C_2))
% 0.21/0.57          | ~ (v4_pre_topc @ X16 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.57            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 0.21/0.57            != (k1_tarski @ sk_C_2)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.21/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (v2_tex_2 @ X12 @ X13)
% 0.21/0.57          | (v4_pre_topc @ (sk_D @ X14 @ X12 @ X13) @ X13)
% 0.21/0.57          | ~ (r1_tarski @ X14 @ X12)
% 0.21/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.57          | ~ (l1_pre_topc @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.57          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.57  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('47', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.57          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '48'])).
% 0.21/0.57  thf('50', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.57         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_2))),
% 0.21/0.57      inference('demod', [status(thm)], ['41', '51'])).
% 0.21/0.57  thf('53', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['29', '52'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

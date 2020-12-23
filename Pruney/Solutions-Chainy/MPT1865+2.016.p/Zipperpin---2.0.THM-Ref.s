%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RZcrWyUZ0w

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:22 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 140 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  558 (2045 expanded)
%              Number of equality atoms :   11 (  49 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ ( sk_D @ X14 @ X12 @ X13 ) )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    r2_hidden @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_2 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_2 ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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
    inference('sup-',[status(thm)],['6','7'])).

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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RZcrWyUZ0w
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:32:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 172 iterations in 0.115s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(t33_tex_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.57             ( ![C:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.39/0.57                      ( ![D:$i]:
% 0.39/0.57                        ( ( m1_subset_1 @
% 0.39/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.57                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.57                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( l1_pre_topc @ A ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57              ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.57                ( ![C:$i]:
% 0.39/0.57                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.57                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.39/0.57                         ( ![D:$i]:
% 0.39/0.57                           ( ( m1_subset_1 @
% 0.39/0.57                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.57                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.57                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.39/0.57  thf('0', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t3_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.57  thf(d3_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.57          | (r2_hidden @ X0 @ X2)
% 0.39/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.57  thf('6', plain, ((r2_hidden @ sk_C_2 @ (u1_struct_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '5'])).
% 0.39/0.57  thf(t63_subset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.57       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.39/0.57          | ~ (r2_hidden @ X7 @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d6_tex_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( l1_pre_topc @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57           ( ( v2_tex_2 @ B @ A ) <=>
% 0.39/0.57             ( ![C:$i]:
% 0.39/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.39/0.57                      ( ![D:$i]:
% 0.39/0.57                        ( ( m1_subset_1 @
% 0.39/0.57                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.57                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.57                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.57                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | ~ (v2_tex_2 @ X12 @ X13)
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ 
% 0.39/0.57              (sk_D @ X14 @ X12 @ X13)) = (X14))
% 0.39/0.57          | ~ (r1_tarski @ X14 @ X12)
% 0.39/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | ~ (l1_pre_topc @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.57              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.39/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.57  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('13', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.57          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.57              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.39/0.57      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.57          (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))
% 0.39/0.57        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '14'])).
% 0.39/0.57  thf('16', plain, ((r2_hidden @ sk_C_2 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.39/0.57          | ~ (r2_hidden @ X7 @ X8))),
% 0.39/0.57      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X9 : $i, X10 : $i]:
% 0.39/0.57         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.39/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.57  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.57         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_2))),
% 0.39/0.57      inference('demod', [status(thm)], ['15', '20'])).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | ~ (v2_tex_2 @ X12 @ X13)
% 0.39/0.57          | (m1_subset_1 @ (sk_D @ X14 @ X12 @ X13) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | ~ (r1_tarski @ X14 @ X12)
% 0.39/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | ~ (l1_pre_topc @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.57  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.57          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.39/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['22', '28'])).
% 0.39/0.57  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X16 : $i]:
% 0.39/0.57         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X16)
% 0.39/0.57            != (k1_tarski @ sk_C_2))
% 0.39/0.57          | ~ (v4_pre_topc @ X16 @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.39/0.57        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.57            (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A))
% 0.39/0.57            != (k1_tarski @ sk_C_2)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      ((m1_subset_1 @ (k1_tarski @ sk_C_2) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('36', plain,
% 0.39/0.57      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | ~ (v2_tex_2 @ X12 @ X13)
% 0.39/0.57          | (v4_pre_topc @ (sk_D @ X14 @ X12 @ X13) @ X13)
% 0.39/0.57          | ~ (r1_tarski @ X14 @ X12)
% 0.39/0.57          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.57          | ~ (l1_pre_topc @ X13))),
% 0.39/0.57      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (l1_pre_topc @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.57          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.39/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.57  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('40', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.57          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)
% 0.39/0.57        | ~ (r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['34', '40'])).
% 0.39/0.57  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_2) @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A) @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.57         (sk_D @ (k1_tarski @ sk_C_2) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_2))),
% 0.39/0.57      inference('demod', [status(thm)], ['33', '43'])).
% 0.39/0.57  thf('45', plain, ($false),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['21', '44'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

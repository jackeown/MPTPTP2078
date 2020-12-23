%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vk3g9Jcgrg

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 196 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  618 (2947 expanded)
%              Number of equality atoms :   19 (  97 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X5 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X5 @ X8 ) ) ),
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
    ! [X2: $i] :
      ( ( k2_tarski @ X2 @ X2 )
      = ( k1_tarski @ X2 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( m1_subset_1 @ ( sk_D @ X17 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('25',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X19: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X19 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X19 @ sk_A )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( v3_pre_topc @ ( sk_D @ X17 @ X15 @ X16 ) @ X16 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('37',plain,(
    v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v2_tex_2 @ X15 @ X16 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ ( sk_D @ X17 @ X15 @ X16 ) )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('47',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ( k1_tarski @ sk_C_1 )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','37','47'])).

thf('49',plain,(
    $false ),
    inference(simplify,[status(thm)],['48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vk3g9Jcgrg
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:53:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 91 iterations in 0.060s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.52  thf(t32_tex_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.52             ( ![C:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.52                      ( ![D:$i]:
% 0.21/0.52                        ( ( m1_subset_1 @
% 0.21/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.52                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.52                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( l1_pre_topc @ A ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52              ( ( v2_tex_2 @ B @ A ) =>
% 0.21/0.52                ( ![C:$i]:
% 0.21/0.52                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.52                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.21/0.52                         ( ![D:$i]:
% 0.21/0.52                           ( ( m1_subset_1 @
% 0.21/0.52                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.52                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.52                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.21/0.52  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t38_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.21/0.52         ((r1_tarski @ (k2_tarski @ X5 @ X7) @ X8)
% 0.21/0.52          | ~ (r2_hidden @ X7 @ X8)
% 0.21/0.52          | ~ (r2_hidden @ X5 @ X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X0 @ sk_B)
% 0.21/0.52          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.52  thf(t69_enumset1, axiom,
% 0.21/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.52  thf('5', plain, (![X2 : $i]: ((k2_tarski @ X2 @ X2) = (k1_tarski @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.52  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf(t28_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (k1_tarski @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_k9_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (k9_subset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X9))
% 0.21/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X9)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.52         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.52           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.21/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d5_tex_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v2_tex_2 @ B @ A ) <=>
% 0.21/0.52             ( ![C:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.21/0.52                      ( ![D:$i]:
% 0.21/0.52                        ( ( m1_subset_1 @
% 0.21/0.52                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.52                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.21/0.52                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (v2_tex_2 @ X15 @ X16)
% 0.21/0.52          | (m1_subset_1 @ (sk_D @ X17 @ X15 @ X16) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (r1_tarski @ X17 @ X15)
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (l1_pre_topc @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('21', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '22'])).
% 0.21/0.52  thf('24', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X19 : $i]:
% 0.21/0.52         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X19)
% 0.21/0.52            != (k1_tarski @ sk_C_1))
% 0.21/0.52          | ~ (v3_pre_topc @ X19 @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      ((~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.52        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.21/0.52            != (k1_tarski @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '15'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (v2_tex_2 @ X15 @ X16)
% 0.21/0.52          | (v3_pre_topc @ (sk_D @ X17 @ X15 @ X16) @ X16)
% 0.21/0.52          | ~ (r1_tarski @ X17 @ X15)
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (l1_pre_topc @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.21/0.52          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('33', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.21/0.52        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '34'])).
% 0.21/0.52  thf('36', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '15'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (v2_tex_2 @ X15 @ X16)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ X16) @ X15 @ 
% 0.21/0.52              (sk_D @ X17 @ X15 @ X16)) = (X17))
% 0.21/0.52          | ~ (r1_tarski @ X17 @ X15)
% 0.21/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.52          | ~ (l1_pre_topc @ X16))),
% 0.21/0.52      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.21/0.52          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('43', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.52          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.21/0.52        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '44'])).
% 0.21/0.52  thf('46', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.52         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain, (((k1_tarski @ sk_C_1) != (k1_tarski @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['27', '37', '47'])).
% 0.21/0.52  thf('49', plain, ($false), inference('simplify', [status(thm)], ['48'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

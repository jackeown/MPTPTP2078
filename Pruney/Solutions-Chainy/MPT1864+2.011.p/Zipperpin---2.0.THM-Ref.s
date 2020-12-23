%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cHWcNK3FEE

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 248 expanded)
%              Number of leaves         :   21 (  83 expanded)
%              Depth                    :   11
%              Number of atoms          :  652 (3916 expanded)
%              Number of equality atoms :   21 ( 122 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( sk_D @ X21 @ X19 @ X20 ) )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
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
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ( m1_subset_1 @ ( sk_D @ X21 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('35',plain,(
    ! [X23: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X23 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ( v3_pre_topc @ ( sk_D @ X21 @ X19 @ X20 ) @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('46',plain,(
    v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k3_xboole_0 @ X0 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('49',plain,(
    ( k3_xboole_0 @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cHWcNK3FEE
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 201 iterations in 0.115s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.56  thf(t32_tex_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.56             ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.56                      ( ![D:$i]:
% 0.20/0.56                        ( ( m1_subset_1 @
% 0.20/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.56                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.56                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( l1_pre_topc @ A ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ( v2_tex_2 @ B @ A ) =>
% 0.20/0.56                ( ![C:$i]:
% 0.20/0.56                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.56                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.20/0.56                         ( ![D:$i]:
% 0.20/0.56                           ( ( m1_subset_1 @
% 0.20/0.56                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.56                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.56                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.20/0.56  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(l1_zfmisc_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X8 : $i, X10 : $i]:
% 0.20/0.56         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.20/0.56      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.56  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf(t28_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      (((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (k1_tarski @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_k9_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.56         ((m1_subset_1 @ (k9_subset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 0.20/0.56          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.20/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.20/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.56           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.20/0.56          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '11'])).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d5_tex_2, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ( v2_tex_2 @ B @ A ) <=>
% 0.20/0.56             ( ![C:$i]:
% 0.20/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.20/0.56                      ( ![D:$i]:
% 0.20/0.56                        ( ( m1_subset_1 @
% 0.20/0.56                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.20/0.56                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.20/0.56                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.56          | ~ (v2_tex_2 @ X19 @ X20)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.20/0.56              (sk_D @ X21 @ X19 @ X20)) = (X21))
% 0.20/0.56          | ~ (r1_tarski @ X21 @ X19)
% 0.20/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.56          | ~ (l1_pre_topc @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.56              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.20/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.56  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('17', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.56              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.20/0.56      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.56          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.20/0.56        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['12', '18'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '11'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.56          | ~ (v2_tex_2 @ X19 @ X20)
% 0.20/0.56          | (m1_subset_1 @ (sk_D @ X21 @ X19 @ X20) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.56          | ~ (r1_tarski @ X21 @ X19)
% 0.20/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.56          | ~ (l1_pre_topc @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('25', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.56          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.20/0.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['20', '26'])).
% 0.20/0.56  thf('28', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.20/0.56          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.20/0.56           (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.20/0.56           = (k3_xboole_0 @ X0 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (((k3_xboole_0 @ sk_B @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.20/0.56         = (k1_tarski @ sk_C_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['19', '31', '32'])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.56  thf('35', plain,
% 0.20/0.56      (![X23 : $i]:
% 0.20/0.56         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X23)
% 0.20/0.56            != (k1_tarski @ sk_C_1))
% 0.20/0.56          | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      ((~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.56            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.20/0.56            != (k1_tarski @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['4', '11'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.56          | ~ (v2_tex_2 @ X19 @ X20)
% 0.20/0.56          | (v3_pre_topc @ (sk_D @ X21 @ X19 @ X20) @ X20)
% 0.20/0.56          | ~ (r1_tarski @ X21 @ X19)
% 0.20/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.56          | ~ (l1_pre_topc @ X20))),
% 0.20/0.56      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ sk_A)
% 0.20/0.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.56          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.56          | ~ (r1_tarski @ X0 @ sk_B)
% 0.20/0.56          | (v3_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.20/0.56        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['37', '43'])).
% 0.20/0.56  thf('45', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      ((v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.56      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.56         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['36', '46'])).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.20/0.56           (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.20/0.56           = (k3_xboole_0 @ X0 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (((k3_xboole_0 @ sk_B @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.20/0.56         != (k1_tarski @ sk_C_1))),
% 0.20/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain, ($false),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['33', '49'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

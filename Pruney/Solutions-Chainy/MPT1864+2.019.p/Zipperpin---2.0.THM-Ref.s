%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1syKmF1i0K

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 122 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  595 (1903 expanded)
%              Number of equality atoms :   11 (  47 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

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

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X6 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X3 ) @ X5 )
      | ~ ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X17 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v3_pre_topc @ X17 @ sk_A )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( v3_pre_topc @ ( sk_D @ X15 @ X13 @ X14 ) @ X14 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v3_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tex_2 @ X13 @ X14 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ ( sk_D @ X15 @ X13 @ X14 ) )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','43'])).

thf('45',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1syKmF1i0K
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:06:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 73 iterations in 0.046s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(t32_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.50             ( ![C:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.50                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.22/0.50                      ( ![D:$i]:
% 0.22/0.50                        ( ( m1_subset_1 @
% 0.22/0.50                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.50                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.22/0.50                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( l1_pre_topc @ A ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50              ( ( v2_tex_2 @ B @ A ) =>
% 0.22/0.50                ( ![C:$i]:
% 0.22/0.50                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.50                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.22/0.50                         ( ![D:$i]:
% 0.22/0.50                           ( ( m1_subset_1 @
% 0.22/0.50                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                             ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.50                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.22/0.50                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t32_tex_2])).
% 0.22/0.50  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t5_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X10 @ X11)
% 0.22/0.50          | ~ (v1_xboole_0 @ X12)
% 0.22/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t2_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]:
% 0.22/0.50         ((r2_hidden @ X8 @ X9)
% 0.22/0.50          | (v1_xboole_0 @ X9)
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf(t63_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ B ) =>
% 0.22/0.50       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (k1_tarski @ X6) @ (k1_zfmisc_1 @ X7))
% 0.22/0.50          | ~ (r2_hidden @ X6 @ X7))),
% 0.22/0.50      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.22/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d5_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v2_tex_2 @ B @ A ) <=>
% 0.22/0.50             ( ![C:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.22/0.50                      ( ![D:$i]:
% 0.22/0.50                        ( ( m1_subset_1 @
% 0.22/0.50                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.22/0.50                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.22/0.51                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (v2_tex_2 @ X13 @ X14)
% 0.22/0.51          | (m1_subset_1 @ (sk_D @ X15 @ X13 @ X14) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (r1_tarski @ X15 @ X13)
% 0.22/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (l1_pre_topc @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('13', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.22/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '14'])).
% 0.22/0.51  thf('16', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(l1_zfmisc_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X3 : $i, X5 : $i]:
% 0.22/0.51         ((r1_tarski @ (k1_tarski @ X3) @ X5) | ~ (r2_hidden @ X3 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.51  thf('18', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('demod', [status(thm)], ['15', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X17 : $i]:
% 0.22/0.51         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X17)
% 0.22/0.51            != (k1_tarski @ sk_C_1))
% 0.22/0.51          | ~ (v3_pre_topc @ X17 @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | ~ (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.22/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.22/0.51            != (k1_tarski @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (v2_tex_2 @ X13 @ X14)
% 0.22/0.51          | (v3_pre_topc @ (sk_D @ X15 @ X13 @ X14) @ X14)
% 0.22/0.51          | ~ (r1_tarski @ X15 @ X13)
% 0.22/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (l1_pre_topc @ X14))),
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
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.22/0.51        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '28'])).
% 0.22/0.51  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (v3_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_1))
% 0.22/0.51        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('clc', [status(thm)], ['21', '31'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.22/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (v2_tex_2 @ X13 @ X14)
% 0.22/0.51          | ((k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ 
% 0.22/0.51              (sk_D @ X15 @ X13 @ X14)) = (X15))
% 0.22/0.51          | ~ (r1_tarski @ X15 @ X13)
% 0.22/0.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.51          | ~ (l1_pre_topc @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ sk_A)
% 0.22/0.51          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.22/0.51          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.51  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('38', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.51          | ~ (r1_tarski @ X0 @ sk_B)
% 0.22/0.51          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.22/0.51        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['33', '39'])).
% 0.22/0.51  thf('41', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.51        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.22/0.51            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.51  thf('43', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.22/0.51      inference('clc', [status(thm)], ['32', '42'])).
% 0.22/0.51  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['3', '43'])).
% 0.22/0.51  thf('45', plain, ($false), inference('sup-', [status(thm)], ['0', '44'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

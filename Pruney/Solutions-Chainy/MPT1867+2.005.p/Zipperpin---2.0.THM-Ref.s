%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vzZzfR825B

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:26 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 116 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  505 ( 829 expanded)
%              Number of equality atoms :   32 (  41 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v4_pre_topc @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('17',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X25 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ X27 )
       != ( sk_C @ X24 @ X25 ) )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['19','32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( sk_C @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','33'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ ( sk_C @ X24 @ X25 ) @ X24 )
      | ( v2_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36','50'])).

thf('52',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['4','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vzZzfR825B
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.21/3.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.21/3.43  % Solved by: fo/fo7.sh
% 3.21/3.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.21/3.43  % done 7923 iterations in 2.963s
% 3.21/3.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.21/3.43  % SZS output start Refutation
% 3.21/3.43  thf(sk_A_type, type, sk_A: $i).
% 3.21/3.43  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.21/3.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.21/3.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.21/3.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.21/3.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.21/3.43  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.21/3.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.21/3.43  thf(sk_B_type, type, sk_B: $i).
% 3.21/3.43  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 3.21/3.43  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.21/3.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.21/3.43  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 3.21/3.43  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.21/3.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.21/3.43  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.21/3.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.21/3.43  thf(t35_tex_2, conjecture,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.21/3.43       ( ![B:$i]:
% 3.21/3.43         ( ( ( v1_xboole_0 @ B ) & 
% 3.21/3.43             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.21/3.43           ( v2_tex_2 @ B @ A ) ) ) ))).
% 3.21/3.43  thf(zf_stmt_0, negated_conjecture,
% 3.21/3.43    (~( ![A:$i]:
% 3.21/3.43        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 3.21/3.43            ( l1_pre_topc @ A ) ) =>
% 3.21/3.43          ( ![B:$i]:
% 3.21/3.43            ( ( ( v1_xboole_0 @ B ) & 
% 3.21/3.43                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.21/3.43              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 3.21/3.43    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 3.21/3.43  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(l13_xboole_0, axiom,
% 3.21/3.43    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.21/3.43  thf('2', plain,
% 3.21/3.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.21/3.43  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['1', '2'])).
% 3.21/3.43  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 3.21/3.43      inference('demod', [status(thm)], ['0', '3'])).
% 3.21/3.43  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('6', plain,
% 3.21/3.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.21/3.43  thf(t4_subset_1, axiom,
% 3.21/3.43    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.21/3.43  thf('7', plain,
% 3.21/3.43      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 3.21/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.21/3.43  thf('8', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup+', [status(thm)], ['6', '7'])).
% 3.21/3.43  thf(cc2_pre_topc, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.21/3.43       ( ![B:$i]:
% 3.21/3.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.21/3.43           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 3.21/3.43  thf('9', plain,
% 3.21/3.43      (![X22 : $i, X23 : $i]:
% 3.21/3.43         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 3.21/3.43          | (v4_pre_topc @ X22 @ X23)
% 3.21/3.43          | ~ (v1_xboole_0 @ X22)
% 3.21/3.43          | ~ (l1_pre_topc @ X23)
% 3.21/3.43          | ~ (v2_pre_topc @ X23))),
% 3.21/3.43      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 3.21/3.43  thf('10', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ X1)
% 3.21/3.43          | ~ (v2_pre_topc @ X0)
% 3.21/3.43          | ~ (l1_pre_topc @ X0)
% 3.21/3.43          | ~ (v1_xboole_0 @ X1)
% 3.21/3.43          | (v4_pre_topc @ X1 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['8', '9'])).
% 3.21/3.43  thf('11', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         ((v4_pre_topc @ X1 @ X0)
% 3.21/3.43          | ~ (l1_pre_topc @ X0)
% 3.21/3.43          | ~ (v2_pre_topc @ X0)
% 3.21/3.43          | ~ (v1_xboole_0 @ X1))),
% 3.21/3.43      inference('simplify', [status(thm)], ['10'])).
% 3.21/3.43  thf('12', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ X0)
% 3.21/3.43          | ~ (v2_pre_topc @ sk_A)
% 3.21/3.43          | (v4_pre_topc @ X0 @ sk_A))),
% 3.21/3.43      inference('sup-', [status(thm)], ['5', '11'])).
% 3.21/3.43  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('14', plain,
% 3.21/3.43      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 3.21/3.43      inference('demod', [status(thm)], ['12', '13'])).
% 3.21/3.43  thf('15', plain,
% 3.21/3.43      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 3.21/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.21/3.43  thf('16', plain,
% 3.21/3.43      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 3.21/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.21/3.43  thf(d6_tex_2, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( l1_pre_topc @ A ) =>
% 3.21/3.43       ( ![B:$i]:
% 3.21/3.43         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.21/3.43           ( ( v2_tex_2 @ B @ A ) <=>
% 3.21/3.43             ( ![C:$i]:
% 3.21/3.43               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.21/3.43                 ( ~( ( r1_tarski @ C @ B ) & 
% 3.21/3.43                      ( ![D:$i]:
% 3.21/3.43                        ( ( m1_subset_1 @
% 3.21/3.43                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.21/3.43                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 3.21/3.43                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 3.21/3.43                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 3.21/3.43  thf('17', plain,
% 3.21/3.43      (![X24 : $i, X25 : $i, X27 : $i]:
% 3.21/3.43         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.21/3.43          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.21/3.43          | ~ (v4_pre_topc @ X27 @ X25)
% 3.21/3.43          | ((k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ X27)
% 3.21/3.43              != (sk_C @ X24 @ X25))
% 3.21/3.43          | (v2_tex_2 @ X24 @ X25)
% 3.21/3.43          | ~ (l1_pre_topc @ X25))),
% 3.21/3.43      inference('cnf', [status(esa)], [d6_tex_2])).
% 3.21/3.43  thf('18', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (l1_pre_topc @ X0)
% 3.21/3.43          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 3.21/3.43          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 3.21/3.43              != (sk_C @ k1_xboole_0 @ X0))
% 3.21/3.43          | ~ (v4_pre_topc @ X1 @ X0)
% 3.21/3.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 3.21/3.43      inference('sup-', [status(thm)], ['16', '17'])).
% 3.21/3.43  thf('19', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 3.21/3.43          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ k1_xboole_0)
% 3.21/3.43              != (sk_C @ k1_xboole_0 @ X0))
% 3.21/3.43          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 3.21/3.43          | ~ (l1_pre_topc @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['15', '18'])).
% 3.21/3.43  thf('20', plain,
% 3.21/3.43      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 3.21/3.43      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.21/3.43  thf(redefinition_k9_subset_1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.21/3.43       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 3.21/3.43  thf('21', plain,
% 3.21/3.43      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.21/3.43         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 3.21/3.43          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.21/3.43      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 3.21/3.43  thf('22', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 3.21/3.43           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['20', '21'])).
% 3.21/3.43  thf(t3_boole, axiom,
% 3.21/3.43    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.21/3.43  thf('23', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 3.21/3.43      inference('cnf', [status(esa)], [t3_boole])).
% 3.21/3.43  thf(t48_xboole_1, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.21/3.43  thf('24', plain,
% 3.21/3.43      (![X8 : $i, X9 : $i]:
% 3.21/3.43         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 3.21/3.43           = (k3_xboole_0 @ X8 @ X9))),
% 3.21/3.43      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.21/3.43  thf('25', plain,
% 3.21/3.43      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.21/3.43      inference('sup+', [status(thm)], ['23', '24'])).
% 3.21/3.43  thf('26', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 3.21/3.43      inference('cnf', [status(esa)], [t3_boole])).
% 3.21/3.43  thf(t36_xboole_1, axiom,
% 3.21/3.43    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.21/3.43  thf('27', plain,
% 3.21/3.43      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 3.21/3.43      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.21/3.43  thf('28', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.21/3.43      inference('sup+', [status(thm)], ['26', '27'])).
% 3.21/3.43  thf(l32_xboole_1, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.21/3.43  thf('29', plain,
% 3.21/3.43      (![X1 : $i, X3 : $i]:
% 3.21/3.43         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 3.21/3.43      inference('cnf', [status(esa)], [l32_xboole_1])).
% 3.21/3.43  thf('30', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['28', '29'])).
% 3.21/3.43  thf('31', plain,
% 3.21/3.43      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.21/3.43      inference('demod', [status(thm)], ['25', '30'])).
% 3.21/3.43  thf('32', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.43      inference('demod', [status(thm)], ['22', '31'])).
% 3.21/3.43  thf('33', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 3.21/3.43          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 3.21/3.43          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 3.21/3.43          | ~ (l1_pre_topc @ X0))),
% 3.21/3.43      inference('demod', [status(thm)], ['19', '32'])).
% 3.21/3.43  thf('34', plain,
% 3.21/3.43      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.21/3.43        | ~ (l1_pre_topc @ sk_A)
% 3.21/3.43        | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 3.21/3.43        | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ sk_A)))),
% 3.21/3.43      inference('sup-', [status(thm)], ['14', '33'])).
% 3.21/3.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.21/3.43  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.21/3.43  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('37', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup+', [status(thm)], ['6', '7'])).
% 3.21/3.43  thf('38', plain,
% 3.21/3.43      (![X24 : $i, X25 : $i]:
% 3.21/3.43         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 3.21/3.43          | (r1_tarski @ (sk_C @ X24 @ X25) @ X24)
% 3.21/3.43          | (v2_tex_2 @ X24 @ X25)
% 3.21/3.43          | ~ (l1_pre_topc @ X25))),
% 3.21/3.43      inference('cnf', [status(esa)], [d6_tex_2])).
% 3.21/3.43  thf('39', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ X1)
% 3.21/3.43          | ~ (l1_pre_topc @ X0)
% 3.21/3.43          | (v2_tex_2 @ X1 @ X0)
% 3.21/3.43          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 3.21/3.43      inference('sup-', [status(thm)], ['37', '38'])).
% 3.21/3.43  thf(t3_xboole_1, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.21/3.43  thf('40', plain,
% 3.21/3.43      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 3.21/3.43      inference('cnf', [status(esa)], [t3_xboole_1])).
% 3.21/3.43  thf('41', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 3.21/3.43          | ~ (l1_pre_topc @ X0)
% 3.21/3.43          | ~ (v1_xboole_0 @ k1_xboole_0)
% 3.21/3.43          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 3.21/3.43      inference('sup-', [status(thm)], ['39', '40'])).
% 3.21/3.43  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.21/3.43  thf('43', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 3.21/3.43          | ~ (l1_pre_topc @ X0)
% 3.21/3.43          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 3.21/3.43      inference('demod', [status(thm)], ['41', '42'])).
% 3.21/3.43  thf('44', plain,
% 3.21/3.43      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.21/3.43  thf('45', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 3.21/3.43      inference('demod', [status(thm)], ['0', '3'])).
% 3.21/3.43  thf('46', plain,
% 3.21/3.43      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['44', '45'])).
% 3.21/3.43  thf('47', plain,
% 3.21/3.43      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 3.21/3.43        | ~ (l1_pre_topc @ sk_A)
% 3.21/3.43        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['43', '46'])).
% 3.21/3.43  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.21/3.43  thf('50', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 3.21/3.43      inference('demod', [status(thm)], ['47', '48', '49'])).
% 3.21/3.43  thf('51', plain,
% 3.21/3.43      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 3.21/3.43      inference('demod', [status(thm)], ['34', '35', '36', '50'])).
% 3.21/3.43  thf('52', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 3.21/3.43      inference('simplify', [status(thm)], ['51'])).
% 3.21/3.43  thf('53', plain, ($false), inference('demod', [status(thm)], ['4', '52'])).
% 3.21/3.43  
% 3.21/3.43  % SZS output end Refutation
% 3.21/3.43  
% 3.21/3.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

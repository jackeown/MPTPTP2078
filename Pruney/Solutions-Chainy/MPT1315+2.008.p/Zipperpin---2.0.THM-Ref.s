%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1cUfopKx8w

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:34 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 155 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  494 (1705 expanded)
%              Number of equality atoms :   27 (  90 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t34_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v4_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_2])).

thf('0',plain,(
    ~ ( v4_pre_topc @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('4',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X22 @ X20 )
        = ( k9_subset_1 @ X21 @ X22 @ ( k3_subset_1 @ X21 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X1 @ k1_xboole_0 )
        = ( k9_subset_1 @ X0 @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X1 @ k1_xboole_0 )
        = ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ k1_xboole_0 )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X17 @ X19 )
        = ( k4_xboole_0 @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,
    ( sk_B
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','20','21'])).

thf('23',plain,
    ( ( sk_B
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['4','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( l1_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('29',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('30',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_B
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf(t43_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v4_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v4_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_pre_topc @ X39 @ X40 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X42 @ ( k2_struct_0 @ X39 ) )
       != X41 )
      | ~ ( v4_pre_topc @ X42 @ X40 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v4_pre_topc @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('33',plain,(
    ! [X39: $i,X40: $i,X42: $i] :
      ( ~ ( l1_pre_topc @ X40 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X42 @ ( k2_struct_0 @ X39 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ X42 @ ( k2_struct_0 @ X39 ) ) @ X39 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( v4_pre_topc @ X42 @ X40 )
      | ~ ( m1_pre_topc @ X39 @ X40 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('36',plain,
    ( sk_B
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ sk_B @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_C )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v4_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['2','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1cUfopKx8w
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 13:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 784 iterations in 0.250s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.70  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.70  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.70  thf(t34_tops_2, conjecture,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_pre_topc @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( m1_pre_topc @ C @ A ) =>
% 0.46/0.70               ( ( v4_pre_topc @ B @ A ) =>
% 0.46/0.70                 ( ![D:$i]:
% 0.46/0.70                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.46/0.70                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i]:
% 0.46/0.70        ( ( l1_pre_topc @ A ) =>
% 0.46/0.70          ( ![B:$i]:
% 0.46/0.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.70              ( ![C:$i]:
% 0.46/0.70                ( ( m1_pre_topc @ C @ A ) =>
% 0.46/0.70                  ( ( v4_pre_topc @ B @ A ) =>
% 0.46/0.70                    ( ![D:$i]:
% 0.46/0.70                      ( ( m1_subset_1 @
% 0.46/0.70                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.46/0.70                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 0.46/0.70  thf('0', plain, (~ (v4_pre_topc @ sk_D_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('1', plain, (((sk_D_1) = (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['0', '1'])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(d3_struct_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (![X33 : $i]:
% 0.46/0.70         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('6', plain, (((sk_D_1) = (sk_B))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf(t4_subset_1, axiom,
% 0.46/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.70  thf('8', plain,
% 0.46/0.70      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.70  thf(t32_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ![C:$i]:
% 0.46/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.46/0.70             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.46/0.70          | ((k7_subset_1 @ X21 @ X22 @ X20)
% 0.46/0.70              = (k9_subset_1 @ X21 @ X22 @ (k3_subset_1 @ X21 @ X20)))
% 0.46/0.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.70          | ((k7_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.46/0.70              = (k9_subset_1 @ X0 @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X29 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.70  thf(d5_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X13 : $i, X14 : $i]:
% 0.46/0.70         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 0.46/0.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf(t3_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.70  thf('14', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.70  thf('15', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.70          | ((k7_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.46/0.70              = (k9_subset_1 @ X0 @ X1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['10', '15'])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (((k7_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ k1_xboole_0)
% 0.46/0.70         = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (u1_struct_0 @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['7', '16'])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.46/0.70          | ((k7_subset_1 @ X18 @ X17 @ X19) = (k4_xboole_0 @ X17 @ X19)))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k7_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0)
% 0.46/0.70           = (k4_xboole_0 @ sk_B @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf('21', plain, (![X2 : $i]: ((k4_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (((sk_B)
% 0.46/0.70         = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (u1_struct_0 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['17', '20', '21'])).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      ((((sk_B)
% 0.46/0.70          = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)))
% 0.46/0.70        | ~ (l1_struct_0 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['4', '22'])).
% 0.46/0.70  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(dt_m1_pre_topc, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_pre_topc @ A ) =>
% 0.46/0.70       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X35 : $i, X36 : $i]:
% 0.46/0.70         (~ (m1_pre_topc @ X35 @ X36)
% 0.46/0.70          | (l1_pre_topc @ X35)
% 0.46/0.70          | ~ (l1_pre_topc @ X36))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.70  thf('26', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('28', plain, ((l1_pre_topc @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf(dt_l1_pre_topc, axiom,
% 0.46/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.70  thf('30', plain, ((l1_struct_0 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (((sk_B)
% 0.46/0.70         = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['23', '30'])).
% 0.46/0.70  thf(t43_pre_topc, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( l1_pre_topc @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.70           ( ![C:$i]:
% 0.46/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.46/0.70               ( ( v4_pre_topc @ C @ B ) <=>
% 0.46/0.70                 ( ?[D:$i]:
% 0.46/0.70                   ( ( ( k9_subset_1 @
% 0.46/0.70                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.46/0.70                       ( C ) ) & 
% 0.46/0.70                     ( v4_pre_topc @ D @ A ) & 
% 0.46/0.70                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.70         (~ (m1_pre_topc @ X39 @ X40)
% 0.46/0.70          | ((k9_subset_1 @ (u1_struct_0 @ X39) @ X42 @ (k2_struct_0 @ X39))
% 0.46/0.70              != (X41))
% 0.46/0.70          | ~ (v4_pre_topc @ X42 @ X40)
% 0.46/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.46/0.70          | (v4_pre_topc @ X41 @ X39)
% 0.46/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.46/0.70          | ~ (l1_pre_topc @ X40))),
% 0.46/0.70      inference('cnf', [status(esa)], [t43_pre_topc])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X39 : $i, X40 : $i, X42 : $i]:
% 0.46/0.70         (~ (l1_pre_topc @ X40)
% 0.46/0.70          | ~ (m1_subset_1 @ 
% 0.46/0.70               (k9_subset_1 @ (u1_struct_0 @ X39) @ X42 @ (k2_struct_0 @ X39)) @ 
% 0.46/0.70               (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.46/0.70          | (v4_pre_topc @ 
% 0.46/0.70             (k9_subset_1 @ (u1_struct_0 @ X39) @ X42 @ (k2_struct_0 @ X39)) @ 
% 0.46/0.70             X39)
% 0.46/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 0.46/0.70          | ~ (v4_pre_topc @ X42 @ X40)
% 0.46/0.70          | ~ (m1_pre_topc @ X39 @ X40))),
% 0.46/0.70      inference('simplify', [status(thm)], ['32'])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.46/0.70          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.46/0.70          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.46/0.70          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.70          | (v4_pre_topc @ 
% 0.46/0.70             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.46/0.70             sk_C)
% 0.46/0.70          | ~ (l1_pre_topc @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['31', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (((sk_B)
% 0.46/0.70         = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)))),
% 0.46/0.70      inference('demod', [status(thm)], ['23', '30'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (m1_pre_topc @ sk_C @ X0)
% 0.46/0.70          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.46/0.70          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.46/0.70          | (v4_pre_topc @ sk_B @ sk_C)
% 0.46/0.70          | ~ (l1_pre_topc @ X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.70        | (v4_pre_topc @ sk_B @ sk_C)
% 0.46/0.70        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.46/0.70        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '37'])).
% 0.46/0.70  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('40', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('41', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('42', plain, ((v4_pre_topc @ sk_B @ sk_C)),
% 0.46/0.70      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.46/0.70  thf('43', plain, ($false), inference('demod', [status(thm)], ['2', '42'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

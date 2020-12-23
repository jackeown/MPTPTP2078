%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SafF6hGQob

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:21 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 159 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  581 (2155 expanded)
%              Number of equality atoms :   17 (  67 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ( m1_subset_1 @ ( sk_D @ X20 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('23',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X22: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X22 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X22 @ sk_A )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ( v4_pre_topc @ ( sk_D @ X20 @ X18 @ X19 ) @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('35',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ ( sk_D @ X20 @ X18 @ X19 ) )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('45',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ( k1_tarski @ sk_C_1 )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','35','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SafF6hGQob
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:27:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 678 iterations in 0.268s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.52/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.52/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.72  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.52/0.72  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.52/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.72  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.52/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.52/0.72  thf(t33_tex_2, conjecture,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( l1_pre_topc @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( v2_tex_2 @ B @ A ) =>
% 0.52/0.72             ( ![C:$i]:
% 0.52/0.72               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.72                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.52/0.72                      ( ![D:$i]:
% 0.52/0.72                        ( ( m1_subset_1 @
% 0.52/0.72                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.52/0.72                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.52/0.72                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i]:
% 0.52/0.72        ( ( l1_pre_topc @ A ) =>
% 0.52/0.72          ( ![B:$i]:
% 0.52/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72              ( ( v2_tex_2 @ B @ A ) =>
% 0.52/0.72                ( ![C:$i]:
% 0.52/0.72                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.52/0.72                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.52/0.72                         ( ![D:$i]:
% 0.52/0.72                           ( ( m1_subset_1 @
% 0.52/0.72                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.52/0.72                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.52/0.72                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.52/0.72  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(l1_zfmisc_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (![X10 : $i, X12 : $i]:
% 0.52/0.72         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.52/0.72      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.52/0.72  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf(t28_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      (![X5 : $i, X6 : $i]:
% 0.52/0.72         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      (((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ sk_B) = (k1_tarski @ sk_C_1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)) = (k1_tarski @ sk_C_1))),
% 0.52/0.72      inference('demod', [status(thm)], ['4', '5'])).
% 0.52/0.72  thf('7', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(t3_subset, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i]:
% 0.52/0.72         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.72  thf('9', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.72  thf(t108_xboole_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.52/0.72  thf('10', plain,
% 0.52/0.72      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.72         (~ (r1_tarski @ X2 @ X3) | (r1_tarski @ (k3_xboole_0 @ X2 @ X4) @ X3))),
% 0.52/0.72      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X15 : $i, X17 : $i]:
% 0.52/0.72         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.52/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.72  thf('13', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.52/0.72          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['6', '13'])).
% 0.52/0.72  thf('15', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(d6_tex_2, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( l1_pre_topc @ A ) =>
% 0.52/0.72       ( ![B:$i]:
% 0.52/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72           ( ( v2_tex_2 @ B @ A ) <=>
% 0.52/0.72             ( ![C:$i]:
% 0.52/0.72               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.52/0.72                      ( ![D:$i]:
% 0.52/0.72                        ( ( m1_subset_1 @
% 0.52/0.72                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.52/0.72                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.52/0.72                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.52/0.72                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | ~ (v2_tex_2 @ X18 @ X19)
% 0.52/0.72          | (m1_subset_1 @ (sk_D @ X20 @ X18 @ X19) @ 
% 0.52/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | ~ (r1_tarski @ X20 @ X18)
% 0.52/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | ~ (l1_pre_topc @ X19))),
% 0.52/0.72      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (l1_pre_topc @ sk_A)
% 0.52/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72          | ~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.72          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.52/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.72  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('19', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72          | ~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.72          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.52/0.72             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.52/0.72      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.52/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.52/0.72      inference('sup-', [status(thm)], ['14', '20'])).
% 0.52/0.72  thf('22', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf('23', plain,
% 0.52/0.72      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('demod', [status(thm)], ['21', '22'])).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X22 : $i]:
% 0.52/0.72         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X22)
% 0.52/0.72            != (k1_tarski @ sk_C_1))
% 0.52/0.72          | ~ (v4_pre_topc @ X22 @ sk_A)
% 0.52/0.72          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.52/0.72        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.52/0.72            != (k1_tarski @ sk_C_1)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.72  thf('26', plain,
% 0.52/0.72      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['6', '13'])).
% 0.52/0.72  thf('27', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | ~ (v2_tex_2 @ X18 @ X19)
% 0.52/0.72          | (v4_pre_topc @ (sk_D @ X20 @ X18 @ X19) @ X19)
% 0.52/0.72          | ~ (r1_tarski @ X20 @ X18)
% 0.52/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | ~ (l1_pre_topc @ X19))),
% 0.52/0.72      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (l1_pre_topc @ sk_A)
% 0.52/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72          | ~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.72          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.52/0.72          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.52/0.72  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('31', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('32', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72          | ~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.72          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.52/0.72      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.52/0.72  thf('33', plain,
% 0.52/0.72      (((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.52/0.72        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.52/0.72      inference('sup-', [status(thm)], ['26', '32'])).
% 0.52/0.72  thf('34', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf('35', plain,
% 0.52/0.72      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.52/0.72      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.52/0.72        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('sup+', [status(thm)], ['6', '13'])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | ~ (v2_tex_2 @ X18 @ X19)
% 0.52/0.72          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ 
% 0.52/0.72              (sk_D @ X20 @ X18 @ X19)) = (X20))
% 0.52/0.72          | ~ (r1_tarski @ X20 @ X18)
% 0.52/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.52/0.72          | ~ (l1_pre_topc @ X19))),
% 0.52/0.72      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (l1_pre_topc @ sk_A)
% 0.52/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72          | ~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.72          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.52/0.72          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.52/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.52/0.72  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('41', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      (![X0 : $i]:
% 0.52/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.52/0.72          | ~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.72          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.52/0.72      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.52/0.72  thf('43', plain,
% 0.52/0.72      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.52/0.72        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.52/0.72      inference('sup-', [status(thm)], ['36', '42'])).
% 0.52/0.72  thf('44', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.52/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.72  thf('45', plain,
% 0.52/0.72      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.52/0.72         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.52/0.72      inference('demod', [status(thm)], ['43', '44'])).
% 0.52/0.72  thf('46', plain, (((k1_tarski @ sk_C_1) != (k1_tarski @ sk_C_1))),
% 0.52/0.72      inference('demod', [status(thm)], ['25', '35', '45'])).
% 0.52/0.72  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

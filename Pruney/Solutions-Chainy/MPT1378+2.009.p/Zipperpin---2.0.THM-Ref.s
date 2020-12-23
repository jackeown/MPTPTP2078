%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvHY3WFBm6

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:46 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 139 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  654 (2446 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(t3_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( m1_connsp_2 @ C @ A @ B )
                      & ( m1_connsp_2 @ D @ A @ B ) )
                   => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( m1_connsp_2 @ C @ A @ B )
                        & ( m1_connsp_2 @ D @ A @ B ) )
                     => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X23 @ X22 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k4_subset_1 @ X26 @ X25 @ X27 )
        = ( k2_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('19',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ ( k1_tops_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['21','36'])).

thf('38',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_hidden @ X31 @ ( k1_tops_1 @ X32 @ X33 ) )
      | ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('49',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['46','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvHY3WFBm6
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:47:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 611 iterations in 0.385s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.82  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.82  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.59/0.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.59/0.82  thf(t3_connsp_2, conjecture,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.82           ( ![C:$i]:
% 0.59/0.82             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.82               ( ![D:$i]:
% 0.59/0.82                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.82                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.59/0.82                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.59/0.82                     ( m1_connsp_2 @
% 0.59/0.82                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i]:
% 0.59/0.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.82            ( l1_pre_topc @ A ) ) =>
% 0.59/0.82          ( ![B:$i]:
% 0.59/0.82            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.82              ( ![C:$i]:
% 0.59/0.82                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.82                  ( ![D:$i]:
% 0.59/0.83                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.59/0.83                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.59/0.83                        ( m1_connsp_2 @
% 0.59/0.83                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 0.59/0.83  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('1', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(dt_k4_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.59/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.83       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.59/0.83          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23))
% 0.59/0.83          | (m1_subset_1 @ (k4_subset_1 @ X23 @ X22 @ X24) @ 
% 0.59/0.83             (k1_zfmisc_1 @ X23)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.59/0.83  thf('4', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.59/0.83           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.83  thf('5', plain,
% 0.59/0.83      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 0.59/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['1', '4'])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('7', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(redefinition_k4_subset_1, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.59/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.83       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.59/0.83  thf('8', plain,
% 0.59/0.83      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.59/0.83          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26))
% 0.59/0.83          | ((k4_subset_1 @ X26 @ X25 @ X27) = (k2_xboole_0 @ X25 @ X27)))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.59/0.83  thf('9', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.59/0.83            = (k2_xboole_0 @ sk_C @ X0))
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 0.59/0.83         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['6', '9'])).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 0.59/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['5', '10'])).
% 0.59/0.83  thf('12', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(t48_tops_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( l1_pre_topc @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83           ( ![C:$i]:
% 0.59/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83               ( ( r1_tarski @ B @ C ) =>
% 0.59/0.83                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.59/0.83  thf('13', plain,
% 0.59/0.83      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.59/0.83          | ~ (r1_tarski @ X28 @ X30)
% 0.59/0.83          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 0.59/0.83          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.59/0.83          | ~ (l1_pre_topc @ X29))),
% 0.59/0.83      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.83          | ~ (r1_tarski @ sk_C @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.59/0.83  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.83          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.83          | ~ (r1_tarski @ sk_C @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 0.59/0.83        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.59/0.83           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['11', '16'])).
% 0.59/0.83  thf(t7_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.59/0.83  thf('18', plain,
% 0.59/0.83      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.59/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.59/0.83  thf('19', plain,
% 0.59/0.83      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.59/0.83        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.59/0.83      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.83  thf(t12_xboole_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i]:
% 0.59/0.83         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 0.59/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.59/0.83         (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 0.59/0.83         = (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.83  thf('22', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(d1_connsp_2, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.83           ( ![C:$i]:
% 0.59/0.83             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.83               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.59/0.83                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.59/0.83          | ~ (m1_connsp_2 @ X33 @ X32 @ X31)
% 0.59/0.83          | (r2_hidden @ X31 @ (k1_tops_1 @ X32 @ X33))
% 0.59/0.83          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.59/0.83          | ~ (l1_pre_topc @ X32)
% 0.59/0.83          | ~ (v2_pre_topc @ X32)
% 0.59/0.83          | (v2_struct_0 @ X32))),
% 0.59/0.83      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.59/0.83  thf('25', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.59/0.83          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.83  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.59/0.83          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.59/0.83        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.59/0.83        | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['22', '28'])).
% 0.59/0.83  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('33', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.59/0.83      inference('clc', [status(thm)], ['31', '32'])).
% 0.59/0.83  thf(d3_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i]:
% 0.59/0.83     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.59/0.83       ( ![D:$i]:
% 0.59/0.83         ( ( r2_hidden @ D @ C ) <=>
% 0.59/0.83           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.83         (~ (r2_hidden @ X0 @ X3)
% 0.59/0.83          | (r2_hidden @ X0 @ X2)
% 0.59/0.83          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.59/0.83  thf('35', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.59/0.83         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.59/0.83      inference('simplify', [status(thm)], ['34'])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (r2_hidden @ sk_B @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['33', '35'])).
% 0.59/0.83  thf('37', plain,
% 0.59/0.83      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['21', '36'])).
% 0.59/0.83  thf('38', plain,
% 0.59/0.83      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 0.59/0.83        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['5', '10'])).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X32))
% 0.59/0.83          | ~ (r2_hidden @ X31 @ (k1_tops_1 @ X32 @ X33))
% 0.59/0.83          | (m1_connsp_2 @ X33 @ X32 @ X31)
% 0.59/0.83          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.59/0.83          | ~ (l1_pre_topc @ X32)
% 0.59/0.83          | ~ (v2_pre_topc @ X32)
% 0.59/0.83          | (v2_struct_0 @ X32))),
% 0.59/0.83      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 0.59/0.83          | ~ (r2_hidden @ X0 @ 
% 0.59/0.83               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.83  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('43', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 0.59/0.83          | ~ (r2_hidden @ X0 @ 
% 0.59/0.83               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.83      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.59/0.83  thf('44', plain,
% 0.59/0.83      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.59/0.83        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 0.59/0.83        | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['37', '43'])).
% 0.59/0.83  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 0.59/0.83        | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['44', '45'])).
% 0.59/0.83  thf('47', plain,
% 0.59/0.83      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 0.59/0.83          sk_A @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('48', plain,
% 0.59/0.83      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 0.59/0.83         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['6', '9'])).
% 0.59/0.83  thf('49', plain,
% 0.59/0.83      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)),
% 0.59/0.83      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.83  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('clc', [status(thm)], ['46', '49'])).
% 0.59/0.83  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.59/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

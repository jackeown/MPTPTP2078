%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gwxULwC2EA

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  96 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  588 (2628 expanded)
%              Number of equality atoms :    7 (  41 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_pre_topc_type,type,(
    v5_pre_topc: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t25_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v2_pre_topc @ B )
            & ( l1_pre_topc @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( v1_compts_1 @ A )
                  & ( v8_pre_topc @ B )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v5_pre_topc @ C @ A @ B ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( v4_pre_topc @ D @ A )
                     => ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v2_pre_topc @ B )
              & ( l1_pre_topc @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( v1_compts_1 @ A )
                    & ( v8_pre_topc @ B )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v5_pre_topc @ C @ A @ B ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( v4_pre_topc @ D @ A )
                       => ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_compts_1])).

thf('0',plain,(
    ~ ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( l1_pre_topc @ C ) )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) )
                 => ( ( ( v5_pre_topc @ D @ A @ C )
                      & ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D )
                        = ( k2_struct_0 @ C ) )
                      & ( v2_compts_1 @ B @ A ) )
                   => ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X11 ) @ X10 @ X8 ) @ X11 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X11 ) @ X10 )
       != ( k2_struct_0 @ X11 ) )
      | ~ ( v5_pre_topc @ X10 @ X9 @ X11 )
      | ~ ( v2_compts_1 @ X8 @ X9 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t24_compts_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v5_pre_topc @ sk_C @ sk_A @ sk_B )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v5_pre_topc @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( ( k2_struct_0 @ sk_B )
       != ( k2_struct_0 @ sk_B ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( v2_compts_1 @ sk_D @ sk_A )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v1_compts_1 @ A )
              & ( v4_pre_topc @ B @ A ) )
           => ( v2_compts_1 @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( v2_compts_1 @ X6 @ X7 )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ~ ( v1_compts_1 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t17_compts_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_compts_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_D @ sk_A )
    | ( v2_compts_1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_compts_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_compts_1 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['13','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X1 @ X2 @ X0 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v4_pre_topc @ X4 @ X5 )
      | ~ ( v2_compts_1 @ X4 @ X5 )
      | ~ ( v8_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v8_pre_topc @ sk_B )
      | ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v8_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v2_compts_1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B )
      | ( v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    v4_pre_topc @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['23','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['0','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gwxULwC2EA
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 25 iterations in 0.019s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.47  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.20/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.47  thf(v5_pre_topc_type, type, v5_pre_topc: $i > $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.20/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(t25_compts_1, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47             ( l1_pre_topc @ B ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.47                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.47                 ( m1_subset_1 @
% 0.20/0.47                   C @ 
% 0.20/0.47                   ( k1_zfmisc_1 @
% 0.20/0.47                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.47               ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.20/0.47                   ( ( k2_relset_1 @
% 0.20/0.47                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.47                     ( k2_struct_0 @ B ) ) & 
% 0.20/0.47                   ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.20/0.47                 ( ![D:$i]:
% 0.20/0.47                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                     ( ( v4_pre_topc @ D @ A ) =>
% 0.20/0.47                       ( v4_pre_topc @
% 0.20/0.47                         ( k7_relset_1 @
% 0.20/0.47                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.20/0.47                         B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.47                ( l1_pre_topc @ B ) ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.47                    ( v1_funct_2 @
% 0.20/0.47                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.47                    ( m1_subset_1 @
% 0.20/0.47                      C @ 
% 0.20/0.47                      ( k1_zfmisc_1 @
% 0.20/0.47                        ( k2_zfmisc_1 @
% 0.20/0.47                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.47                  ( ( ( v1_compts_1 @ A ) & ( v8_pre_topc @ B ) & 
% 0.20/0.47                      ( ( k2_relset_1 @
% 0.20/0.47                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.20/0.47                        ( k2_struct_0 @ B ) ) & 
% 0.20/0.47                      ( v5_pre_topc @ C @ A @ B ) ) =>
% 0.20/0.47                    ( ![D:$i]:
% 0.20/0.47                      ( ( m1_subset_1 @
% 0.20/0.47                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47                        ( ( v4_pre_topc @ D @ A ) =>
% 0.20/0.47                          ( v4_pre_topc @
% 0.20/0.47                            ( k7_relset_1 @
% 0.20/0.47                              ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) @ 
% 0.20/0.47                            B ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t25_compts_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (~ (v4_pre_topc @ 
% 0.20/0.47          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.47           sk_D) @ 
% 0.20/0.47          sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_C @ 
% 0.20/0.47        (k1_zfmisc_1 @ 
% 0.20/0.47         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t24_compts_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_pre_topc @ C ) ) =>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.47                     ( v1_funct_2 @
% 0.20/0.47                       D @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) & 
% 0.20/0.47                     ( m1_subset_1 @
% 0.20/0.47                       D @ 
% 0.20/0.47                       ( k1_zfmisc_1 @
% 0.20/0.47                         ( k2_zfmisc_1 @
% 0.20/0.47                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) ) ) ) ) =>
% 0.20/0.47                   ( ( ( v5_pre_topc @ D @ A @ C ) & 
% 0.20/0.47                       ( ( k2_relset_1 @
% 0.20/0.47                           ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D ) =
% 0.20/0.47                         ( k2_struct_0 @ C ) ) & 
% 0.20/0.47                       ( v2_compts_1 @ B @ A ) ) =>
% 0.20/0.47                     ( v2_compts_1 @
% 0.20/0.47                       ( k7_relset_1 @
% 0.20/0.47                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ C ) @ D @ B ) @ 
% 0.20/0.47                       C ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.47          | ~ (v1_funct_1 @ X10)
% 0.20/0.47          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X11))
% 0.20/0.47          | ~ (m1_subset_1 @ X10 @ 
% 0.20/0.47               (k1_zfmisc_1 @ 
% 0.20/0.47                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X11))))
% 0.20/0.47          | (v2_compts_1 @ 
% 0.20/0.47             (k7_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X11) @ X10 @ X8) @ 
% 0.20/0.47             X11)
% 0.20/0.47          | ((k2_relset_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X11) @ X10)
% 0.20/0.47              != (k2_struct_0 @ X11))
% 0.20/0.47          | ~ (v5_pre_topc @ X10 @ X9 @ X11)
% 0.20/0.47          | ~ (v2_compts_1 @ X8 @ X9)
% 0.20/0.47          | ~ (l1_pre_topc @ X11)
% 0.20/0.47          | (v2_struct_0 @ X11)
% 0.20/0.47          | ~ (l1_pre_topc @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [t24_compts_1])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_pre_topc @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.47          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.20/0.47          | ~ (v5_pre_topc @ sk_C @ sk_A @ sk_B)
% 0.20/0.47          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.47              != (k2_struct_0 @ sk_B))
% 0.20/0.47          | (v2_compts_1 @ 
% 0.20/0.47             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.47              sk_C @ X0) @ 
% 0.20/0.47             sk_B)
% 0.20/0.47          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.20/0.47          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, ((v5_pre_topc @ sk_C @ sk_A @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.20/0.47         = (k2_struct_0 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.20/0.47          | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.20/0.47          | (v2_compts_1 @ 
% 0.20/0.47             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.47              sk_C @ X0) @ 
% 0.20/0.47             sk_B)
% 0.20/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '5', '6', '7', '8', '9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.47          | (v2_compts_1 @ 
% 0.20/0.47             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.47              sk_C @ X0) @ 
% 0.20/0.47             sk_B)
% 0.20/0.47          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (((v2_struct_0 @ sk_B)
% 0.20/0.47        | ~ (v2_compts_1 @ sk_D @ sk_A)
% 0.20/0.47        | (v2_compts_1 @ 
% 0.20/0.47           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.47            sk_D) @ 
% 0.20/0.47           sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '12'])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t17_compts_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_pre_topc @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.47           ( ( ( v1_compts_1 @ A ) & ( v4_pre_topc @ B @ A ) ) =>
% 0.20/0.47             ( v2_compts_1 @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | (v2_compts_1 @ X6 @ X7)
% 0.20/0.48          | ~ (v4_pre_topc @ X6 @ X7)
% 0.20/0.48          | ~ (v1_compts_1 @ X7)
% 0.20/0.48          | ~ (l1_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t17_compts_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ~ (v1_compts_1 @ sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ sk_D @ sk_A)
% 0.20/0.48        | (v2_compts_1 @ sk_D @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain, ((v1_compts_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain, ((v4_pre_topc @ sk_D @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain, ((v2_compts_1 @ sk_D @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_B)
% 0.20/0.48        | (v2_compts_1 @ 
% 0.20/0.48           (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.48            sk_D) @ 
% 0.20/0.48           sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '20'])).
% 0.20/0.48  thf('22', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((v2_compts_1 @ 
% 0.20/0.48        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.48         sk_D) @ 
% 0.20/0.48        sk_B)),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ 
% 0.20/0.48        (k1_zfmisc_1 @ 
% 0.20/0.48         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k7_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.20/0.48          | (m1_subset_1 @ (k7_relset_1 @ X1 @ X2 @ X0 @ X3) @ 
% 0.20/0.48             (k1_zfmisc_1 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (m1_subset_1 @ 
% 0.20/0.48          (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.48           X0) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf(t16_compts_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.20/0.48             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.20/0.48          | (v4_pre_topc @ X4 @ X5)
% 0.20/0.48          | ~ (v2_compts_1 @ X4 @ X5)
% 0.20/0.48          | ~ (v8_pre_topc @ X5)
% 0.20/0.48          | ~ (l1_pre_topc @ X5)
% 0.20/0.48          | ~ (v2_pre_topc @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ sk_B)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.48          | ~ (v8_pre_topc @ sk_B)
% 0.20/0.48          | ~ (v2_compts_1 @ 
% 0.20/0.48               (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48                sk_C @ X0) @ 
% 0.20/0.48               sk_B)
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48              sk_C @ X0) @ 
% 0.20/0.48             sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, ((v8_pre_topc @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v2_compts_1 @ 
% 0.20/0.48             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48              sk_C @ X0) @ 
% 0.20/0.48             sk_B)
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.48              sk_C @ X0) @ 
% 0.20/0.48             sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((v4_pre_topc @ 
% 0.20/0.48        (k7_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.20/0.48         sk_D) @ 
% 0.20/0.48        sk_B)),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '32'])).
% 0.20/0.48  thf('34', plain, ($false), inference('demod', [status(thm)], ['0', '33'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

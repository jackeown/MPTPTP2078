%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R8u9Ti4ij

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   53 (  75 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  532 (1192 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_yellow19_type,type,(
    m1_yellow19: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t7_yellow19,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ C ) ) ) @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ C ) ) ) @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_yellow19])).

thf('0',plain,(
    ~ ( m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_waybel_0 @ B @ A )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A )
        & ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_waybel_0 @ X5 @ X6 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) )
      | ( l1_waybel_0 @ ( k4_waybel_9 @ X6 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_waybel_9])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_waybel_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_struct_0 @ X3 )
      | ~ ( l1_waybel_0 @ X4 @ X3 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X3 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('13',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d2_yellow19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_yellow19 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( C
                      = ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ D ) ) @ ( u1_struct_0 @ A ) @ ( u1_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ D ) ) ) )
                    & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( X11
       != ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X9 @ X8 @ X10 ) ) @ ( u1_struct_0 @ X9 ) @ ( u1_waybel_0 @ X9 @ ( k4_waybel_9 @ X9 @ X8 @ X10 ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ( m1_yellow19 @ X11 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_yellow19])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X9 @ X8 @ X10 ) ) @ ( u1_struct_0 @ X9 ) @ ( u1_waybel_0 @ X9 @ ( k4_waybel_9 @ X9 @ X8 @ X10 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ X9 @ X8 @ X10 ) ) @ ( u1_struct_0 @ X9 ) @ ( u1_waybel_0 @ X9 @ ( k4_waybel_9 @ X9 @ X8 @ X10 ) ) ) @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_waybel_0 @ X8 @ X9 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_waybel_0 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) )
    | ( m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) @ sk_A @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_yellow19 @ ( k2_relset_1 @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C ) ) ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0R8u9Ti4ij
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 31 iterations in 0.026s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.44  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.20/0.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.44  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.44  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.44  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.44  thf(k4_waybel_9_type, type, k4_waybel_9: $i > $i > $i > $i).
% 0.20/0.44  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.20/0.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.44  thf(m1_yellow19_type, type, m1_yellow19: $i > $i > $i > $o).
% 0.20/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.44  thf(t7_yellow19, conjecture,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.44           ( ![C:$i]:
% 0.20/0.44             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.44               ( m1_yellow19 @
% 0.20/0.44                 ( k2_relset_1 @
% 0.20/0.44                   ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.20/0.44                   ( u1_struct_0 @ A ) @ 
% 0.20/0.44                   ( u1_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ C ) ) ) @ 
% 0.20/0.44                 A @ B ) ) ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i]:
% 0.20/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44          ( ![B:$i]:
% 0.20/0.44            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.44              ( ![C:$i]:
% 0.20/0.44                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.44                  ( m1_yellow19 @
% 0.20/0.44                    ( k2_relset_1 @
% 0.20/0.44                      ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.20/0.44                      ( u1_struct_0 @ A ) @ 
% 0.20/0.44                      ( u1_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ C ) ) ) @ 
% 0.20/0.44                    A @ B ) ) ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t7_yellow19])).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      (~ (m1_yellow19 @ 
% 0.20/0.44          (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44           (u1_struct_0 @ sk_A) @ 
% 0.20/0.44           (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))) @ 
% 0.20/0.44          sk_A @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(dt_k4_waybel_9, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) & 
% 0.20/0.44         ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) & 
% 0.20/0.44         ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.44       ( ( v6_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) & 
% 0.20/0.44         ( l1_waybel_0 @ ( k4_waybel_9 @ A @ B @ C ) @ A ) ) ))).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.44         (~ (l1_waybel_0 @ X5 @ X6)
% 0.20/0.44          | (v2_struct_0 @ X5)
% 0.20/0.44          | ~ (l1_struct_0 @ X6)
% 0.20/0.44          | (v2_struct_0 @ X6)
% 0.20/0.44          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5))
% 0.20/0.44          | (l1_waybel_0 @ (k4_waybel_9 @ X6 @ X5 @ X7) @ X6))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k4_waybel_9])).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (![X0 : $i]:
% 0.20/0.44         ((l1_waybel_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C) @ X0)
% 0.20/0.44          | (v2_struct_0 @ X0)
% 0.20/0.44          | ~ (l1_struct_0 @ X0)
% 0.20/0.44          | (v2_struct_0 @ sk_B)
% 0.20/0.44          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.20/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.44  thf('5', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_B)
% 0.20/0.44        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ sk_A)
% 0.20/0.44        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.44  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_B)
% 0.20/0.44        | (v2_struct_0 @ sk_A)
% 0.20/0.44        | (l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.44  thf('8', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.44  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('11', plain, ((l1_waybel_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.20/0.44      inference('clc', [status(thm)], ['9', '10'])).
% 0.20/0.44  thf(dt_u1_waybel_0, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.44       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.20/0.44         ( v1_funct_2 @
% 0.20/0.44           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.44         ( m1_subset_1 @
% 0.20/0.44           ( u1_waybel_0 @ A @ B ) @ 
% 0.20/0.44           ( k1_zfmisc_1 @
% 0.20/0.44             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.44  thf('12', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i]:
% 0.20/0.44         (~ (l1_struct_0 @ X3)
% 0.20/0.44          | ~ (l1_waybel_0 @ X4 @ X3)
% 0.20/0.44          | (m1_subset_1 @ (u1_waybel_0 @ X3 @ X4) @ 
% 0.20/0.44             (k1_zfmisc_1 @ 
% 0.20/0.44              (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X3)))))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.20/0.44  thf('13', plain,
% 0.20/0.44      (((m1_subset_1 @ 
% 0.20/0.44         (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44         (k1_zfmisc_1 @ 
% 0.20/0.44          (k2_zfmisc_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44           (u1_struct_0 @ sk_A))))
% 0.20/0.44        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.44  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      ((m1_subset_1 @ 
% 0.20/0.44        (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44        (k1_zfmisc_1 @ 
% 0.20/0.44         (k2_zfmisc_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44          (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.44  thf(dt_k2_relset_1, axiom,
% 0.20/0.44    (![A:$i,B:$i,C:$i]:
% 0.20/0.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.44       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.44         ((m1_subset_1 @ (k2_relset_1 @ X0 @ X1 @ X2) @ (k1_zfmisc_1 @ X1))
% 0.20/0.44          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.44  thf('17', plain,
% 0.20/0.44      ((m1_subset_1 @ 
% 0.20/0.44        (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A) @ 
% 0.20/0.44         (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))) @ 
% 0.20/0.44        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.44  thf(d2_yellow19, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.44           ( ![C:$i]:
% 0.20/0.44             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44               ( ( m1_yellow19 @ C @ A @ B ) <=>
% 0.20/0.44                 ( ?[D:$i]:
% 0.20/0.44                   ( ( ( C ) =
% 0.20/0.44                       ( k2_relset_1 @
% 0.20/0.44                         ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ D ) ) @ 
% 0.20/0.44                         ( u1_struct_0 @ A ) @ 
% 0.20/0.44                         ( u1_waybel_0 @ A @ ( k4_waybel_9 @ A @ B @ D ) ) ) ) & 
% 0.20/0.44                     ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.44  thf('18', plain,
% 0.20/0.44      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.44         ((v2_struct_0 @ X8)
% 0.20/0.44          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.44          | ((X11)
% 0.20/0.44              != (k2_relset_1 @ 
% 0.20/0.44                  (u1_struct_0 @ (k4_waybel_9 @ X9 @ X8 @ X10)) @ 
% 0.20/0.44                  (u1_struct_0 @ X9) @ 
% 0.20/0.44                  (u1_waybel_0 @ X9 @ (k4_waybel_9 @ X9 @ X8 @ X10))))
% 0.20/0.44          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.44          | (m1_yellow19 @ X11 @ X9 @ X8)
% 0.20/0.44          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.44          | ~ (l1_struct_0 @ X9)
% 0.20/0.44          | (v2_struct_0 @ X9))),
% 0.20/0.44      inference('cnf', [status(esa)], [d2_yellow19])).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.44         ((v2_struct_0 @ X9)
% 0.20/0.44          | ~ (l1_struct_0 @ X9)
% 0.20/0.44          | ~ (m1_subset_1 @ 
% 0.20/0.44               (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ X9 @ X8 @ X10)) @ 
% 0.20/0.44                (u1_struct_0 @ X9) @ 
% 0.20/0.44                (u1_waybel_0 @ X9 @ (k4_waybel_9 @ X9 @ X8 @ X10))) @ 
% 0.20/0.44               (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.44          | (m1_yellow19 @ 
% 0.20/0.44             (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ X9 @ X8 @ X10)) @ 
% 0.20/0.44              (u1_struct_0 @ X9) @ 
% 0.20/0.44              (u1_waybel_0 @ X9 @ (k4_waybel_9 @ X9 @ X8 @ X10))) @ 
% 0.20/0.44             X9 @ X8)
% 0.20/0.44          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X8))
% 0.20/0.44          | ~ (l1_waybel_0 @ X8 @ X9)
% 0.20/0.44          | (v2_struct_0 @ X8))),
% 0.20/0.44      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.44  thf('20', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_B)
% 0.20/0.44        | ~ (l1_waybel_0 @ sk_B @ sk_A)
% 0.20/0.44        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))
% 0.20/0.44        | (m1_yellow19 @ 
% 0.20/0.44           (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44            (u1_struct_0 @ sk_A) @ 
% 0.20/0.44            (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))) @ 
% 0.20/0.44           sk_A @ sk_B)
% 0.20/0.44        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.44  thf('21', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('22', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('24', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_B)
% 0.20/0.44        | (m1_yellow19 @ 
% 0.20/0.44           (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44            (u1_struct_0 @ sk_A) @ 
% 0.20/0.44            (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))) @ 
% 0.20/0.44           sk_A @ sk_B)
% 0.20/0.44        | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.20/0.44  thf('25', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('26', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_A)
% 0.20/0.44        | (m1_yellow19 @ 
% 0.20/0.44           (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44            (u1_struct_0 @ sk_A) @ 
% 0.20/0.44            (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))) @ 
% 0.20/0.44           sk_A @ sk_B))),
% 0.20/0.44      inference('clc', [status(thm)], ['24', '25'])).
% 0.20/0.44  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('28', plain,
% 0.20/0.44      ((m1_yellow19 @ 
% 0.20/0.44        (k2_relset_1 @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C)) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A) @ 
% 0.20/0.44         (u1_waybel_0 @ sk_A @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C))) @ 
% 0.20/0.44        sk_A @ sk_B)),
% 0.20/0.44      inference('clc', [status(thm)], ['26', '27'])).
% 0.20/0.44  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

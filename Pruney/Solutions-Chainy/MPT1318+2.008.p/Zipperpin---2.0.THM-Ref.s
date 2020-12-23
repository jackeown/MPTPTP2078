%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OxSmDt7OgA

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:38 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   49 (  66 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :  410 ( 791 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t38_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_tops_2])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X16 @ X15 ) )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X10 @ X11 ) @ ( k3_subset_1 @ X10 @ ( k9_subset_1 @ X10 @ X11 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t42_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X7 @ X6 ) @ ( k3_subset_1 @ X7 @ X8 ) )
      | ( r1_tarski @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('17',plain,
    ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['17','24','25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['6','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OxSmDt7OgA
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:53:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.69/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.93  % Solved by: fo/fo7.sh
% 0.69/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.93  % done 542 iterations in 0.470s
% 0.69/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.93  % SZS output start Refutation
% 0.69/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.93  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.69/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.69/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.93  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.69/0.93  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.69/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.93  thf(t38_tops_2, conjecture,
% 0.69/0.93    (![A:$i]:
% 0.69/0.93     ( ( l1_pre_topc @ A ) =>
% 0.69/0.93       ( ![B:$i]:
% 0.69/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.93           ( ![C:$i]:
% 0.69/0.93             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.93               ( m1_subset_1 @
% 0.69/0.93                 ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.69/0.93                 ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.69/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.93    (~( ![A:$i]:
% 0.69/0.93        ( ( l1_pre_topc @ A ) =>
% 0.69/0.93          ( ![B:$i]:
% 0.69/0.93            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.93              ( ![C:$i]:
% 0.69/0.93                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.93                  ( m1_subset_1 @
% 0.69/0.93                    ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.69/0.93                    ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.69/0.93    inference('cnf.neg', [status(esa)], [t38_tops_2])).
% 0.69/0.93  thf('0', plain,
% 0.69/0.93      (~ (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.93          (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('1', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf(t29_pre_topc, axiom,
% 0.69/0.93    (![A:$i]:
% 0.69/0.93     ( ( l1_pre_topc @ A ) =>
% 0.69/0.93       ( ![B:$i]:
% 0.69/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.93           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.69/0.93  thf('2', plain,
% 0.69/0.93      (![X15 : $i, X16 : $i]:
% 0.69/0.93         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.69/0.93          | ((u1_struct_0 @ (k1_pre_topc @ X16 @ X15)) = (X15))
% 0.69/0.93          | ~ (l1_pre_topc @ X16))),
% 0.69/0.93      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.69/0.93  thf('3', plain,
% 0.69/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.69/0.93        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.93  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('5', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.69/0.93      inference('demod', [status(thm)], ['3', '4'])).
% 0.69/0.93  thf('6', plain,
% 0.69/0.93      (~ (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.93          (k1_zfmisc_1 @ sk_C))),
% 0.69/0.93      inference('demod', [status(thm)], ['0', '5'])).
% 0.69/0.93  thf('7', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('8', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf(t42_subset_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.93       ( ![C:$i]:
% 0.69/0.93         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.93           ( r1_tarski @
% 0.69/0.93             ( k3_subset_1 @ A @ B ) @ 
% 0.69/0.93             ( k3_subset_1 @ A @ ( k9_subset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.69/0.93  thf('9', plain,
% 0.69/0.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.69/0.93         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.69/0.93          | (r1_tarski @ (k3_subset_1 @ X10 @ X11) @ 
% 0.69/0.93             (k3_subset_1 @ X10 @ (k9_subset_1 @ X10 @ X11 @ X9)))
% 0.69/0.93          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t42_subset_1])).
% 0.69/0.93  thf('10', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.93          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.69/0.93             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.93              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B))))),
% 0.69/0.93      inference('sup-', [status(thm)], ['8', '9'])).
% 0.69/0.93  thf('11', plain,
% 0.69/0.93      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.69/0.93        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.93         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['7', '10'])).
% 0.69/0.93  thf('12', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf(commutativity_k9_subset_1, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i]:
% 0.69/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.93       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.69/0.93  thf('13', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.69/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.69/0.93      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.69/0.93  thf('14', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.69/0.93           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.69/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.69/0.93  thf('15', plain,
% 0.69/0.93      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.69/0.93        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.69/0.93         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.69/0.93      inference('demod', [status(thm)], ['11', '14'])).
% 0.69/0.93  thf(t31_subset_1, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.93       ( ![C:$i]:
% 0.69/0.93         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.93           ( ( r1_tarski @ B @ C ) <=>
% 0.69/0.93             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.69/0.93  thf('16', plain,
% 0.69/0.93      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.93         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.69/0.93          | ~ (r1_tarski @ (k3_subset_1 @ X7 @ X6) @ (k3_subset_1 @ X7 @ X8))
% 0.69/0.93          | (r1_tarski @ X8 @ X6)
% 0.69/0.93          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.69/0.93      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.69/0.93  thf('17', plain,
% 0.69/0.93      ((~ (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.93           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.93        | (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.93           sk_C)
% 0.69/0.93        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.93      inference('sup-', [status(thm)], ['15', '16'])).
% 0.69/0.93  thf('18', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('19', plain,
% 0.69/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.93         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.69/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.69/0.93      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.69/0.93  thf('20', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.69/0.93           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.69/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.69/0.93  thf('21', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf(dt_k9_subset_1, axiom,
% 0.69/0.93    (![A:$i,B:$i,C:$i]:
% 0.69/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.93       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.93  thf('22', plain,
% 0.69/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.69/0.93         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.69/0.93          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.69/0.93      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.69/0.93  thf('23', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.69/0.93          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.69/0.93  thf('24', plain,
% 0.69/0.93      (![X0 : $i]:
% 0.69/0.93         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.69/0.93          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('sup+', [status(thm)], ['20', '23'])).
% 0.69/0.93  thf('25', plain,
% 0.69/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.93  thf('26', plain,
% 0.69/0.93      ((r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.69/0.93      inference('demod', [status(thm)], ['17', '24', '25'])).
% 0.69/0.93  thf(t3_subset, axiom,
% 0.69/0.93    (![A:$i,B:$i]:
% 0.69/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.69/0.93  thf('27', plain,
% 0.69/0.93      (![X12 : $i, X14 : $i]:
% 0.69/0.93         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.69/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.69/0.93  thf('28', plain,
% 0.69/0.93      ((m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.69/0.93        (k1_zfmisc_1 @ sk_C))),
% 0.69/0.93      inference('sup-', [status(thm)], ['26', '27'])).
% 0.69/0.93  thf('29', plain, ($false), inference('demod', [status(thm)], ['6', '28'])).
% 0.69/0.93  
% 0.69/0.93  % SZS output end Refutation
% 0.69/0.93  
% 0.80/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

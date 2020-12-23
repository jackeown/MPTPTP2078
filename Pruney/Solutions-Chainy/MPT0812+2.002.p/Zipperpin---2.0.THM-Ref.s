%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.luJxkBPZWA

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  64 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :  192 ( 486 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(r3_wellord1_type,type,(
    r3_wellord1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( r4_wellord1 @ A @ B )
              & ( v2_wellord1 @ A ) )
           => ( v2_wellord1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( ( r4_wellord1 @ A @ B )
                & ( v2_wellord1 @ A ) )
             => ( v2_wellord1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_wellord1])).

thf('0',plain,(
    ~ ( v2_wellord1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
          <=> ? [C: $i] :
                ( ( r3_wellord1 @ A @ B @ C )
                & ( v1_funct_1 @ C )
                & ( v1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( r3_wellord1 @ X1 @ X0 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r3_wellord1 @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t54_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( v2_wellord1 @ A )
                  & ( r3_wellord1 @ A @ B @ C ) )
               => ( v2_wellord1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v2_wellord1 @ X4 )
      | ( v2_wellord1 @ X3 )
      | ~ ( r3_wellord1 @ X4 @ X3 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t54_wellord1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_wellord1 @ sk_B )
    | ~ ( v2_wellord1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r4_wellord1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r4_wellord1 @ X1 @ X0 )
      | ( v1_funct_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_wellord1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v2_wellord1 @ sk_B ),
    inference(demod,[status(thm)],['8','9','15','21','22','23'])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['0','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.luJxkBPZWA
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 13 iterations in 0.010s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.21/0.47  thf(r3_wellord1_type, type, r3_wellord1: $i > $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t65_wellord1, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( ( r4_wellord1 @ A @ B ) & ( v2_wellord1 @ A ) ) =>
% 0.21/0.47             ( v2_wellord1 @ B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( v1_relat_1 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( v1_relat_1 @ B ) =>
% 0.21/0.47              ( ( ( r4_wellord1 @ A @ B ) & ( v2_wellord1 @ A ) ) =>
% 0.21/0.47                ( v2_wellord1 @ B ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t65_wellord1])).
% 0.21/0.47  thf('0', plain, (~ (v2_wellord1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d8_wellord1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ( r4_wellord1 @ A @ B ) <=>
% 0.21/0.47             ( ?[C:$i]:
% 0.21/0.47               ( ( r3_wellord1 @ A @ B @ C ) & ( v1_funct_1 @ C ) & 
% 0.21/0.47                 ( v1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (r4_wellord1 @ X1 @ X0)
% 0.21/0.47          | (r3_wellord1 @ X1 @ X0 @ (sk_C @ X0 @ X1))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | (r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain, ((r3_wellord1 @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf(t54_wellord1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_relat_1 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( v1_relat_1 @ B ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.47               ( ( ( v2_wellord1 @ A ) & ( r3_wellord1 @ A @ B @ C ) ) =>
% 0.21/0.47                 ( v2_wellord1 @ B ) ) ) ) ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X3)
% 0.21/0.47          | ~ (v2_wellord1 @ X4)
% 0.21/0.47          | (v2_wellord1 @ X3)
% 0.21/0.47          | ~ (r3_wellord1 @ X4 @ X3 @ X5)
% 0.21/0.47          | ~ (v1_funct_1 @ X5)
% 0.21/0.47          | ~ (v1_relat_1 @ X5)
% 0.21/0.47          | ~ (v1_relat_1 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t54_wellord1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | ~ (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.47        | ~ (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.47        | (v2_wellord1 @ sk_B)
% 0.21/0.47        | ~ (v2_wellord1 @ sk_A)
% 0.21/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (r4_wellord1 @ X1 @ X0)
% 0.21/0.47          | (v1_relat_1 @ (sk_C @ X0 @ X1))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | (v1_relat_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain, ((v1_relat_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.21/0.47  thf('16', plain, ((r4_wellord1 @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v1_relat_1 @ X0)
% 0.21/0.47          | ~ (r4_wellord1 @ X1 @ X0)
% 0.21/0.47          | (v1_funct_1 @ (sk_C @ X0 @ X1))
% 0.21/0.47          | ~ (v1_relat_1 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_wellord1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((~ (v1_relat_1 @ sk_A)
% 0.21/0.47        | (v1_funct_1 @ (sk_C @ sk_B @ sk_A))
% 0.21/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, ((v1_funct_1 @ (sk_C @ sk_B @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.21/0.47  thf('22', plain, ((v2_wellord1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain, ((v2_wellord1 @ sk_B)),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9', '15', '21', '22', '23'])).
% 0.21/0.47  thf('25', plain, ($false), inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

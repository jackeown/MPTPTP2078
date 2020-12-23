%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pNtU0GNFLC

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:14 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  439 ( 734 expanded)
%              Number of equality atoms :   38 (  55 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X67: $i,X68: $i] :
      ( ( ( k3_subset_1 @ X68 @ ( k3_subset_1 @ X68 @ X67 ) )
        = X67 )
      | ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X62: $i,X63: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X62 @ X63 ) @ ( k1_zfmisc_1 @ X62 ) )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ X62 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('15',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k3_subset_1 @ X60 @ X61 )
        = ( k4_xboole_0 @ X60 @ X61 ) )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['5','18'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X32 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X30 @ X31 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = ( k4_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['2','21'])).

thf('23',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_2 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ X70 ) )
      | ( ( k7_subset_1 @ X70 @ X69 @ X71 )
        = ( k4_xboole_0 @ X69 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_2 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( ( k9_subset_1 @ X57 @ X59 @ X58 )
        = ( k9_subset_1 @ X57 @ X58 @ X59 ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X72: $i,X73: $i,X74: $i] :
      ( ( ( k9_subset_1 @ X74 @ X72 @ X73 )
        = ( k3_xboole_0 @ X72 @ X73 ) )
      | ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_2 )
 != ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['27','34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pNtU0GNFLC
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.40/2.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.40/2.61  % Solved by: fo/fo7.sh
% 2.40/2.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.40/2.61  % done 6071 iterations in 2.153s
% 2.40/2.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.40/2.61  % SZS output start Refutation
% 2.40/2.61  thf(sk_B_type, type, sk_B: $i).
% 2.40/2.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.40/2.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.40/2.61  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.40/2.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.40/2.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.40/2.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.40/2.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.40/2.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.40/2.61  thf(sk_A_type, type, sk_A: $i).
% 2.40/2.61  thf(t32_subset_1, conjecture,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61       ( ![C:$i]:
% 2.40/2.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.40/2.61             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.40/2.61  thf(zf_stmt_0, negated_conjecture,
% 2.40/2.61    (~( ![A:$i,B:$i]:
% 2.40/2.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61          ( ![C:$i]:
% 2.40/2.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61              ( ( k7_subset_1 @ A @ B @ C ) =
% 2.40/2.61                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 2.40/2.61    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 2.40/2.61  thf('0', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf(d5_subset_1, axiom,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.40/2.61  thf('1', plain,
% 2.40/2.61      (![X60 : $i, X61 : $i]:
% 2.40/2.61         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 2.40/2.61          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 2.40/2.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.40/2.61  thf('2', plain,
% 2.40/2.61      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 2.40/2.61      inference('sup-', [status(thm)], ['0', '1'])).
% 2.40/2.61  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf(involutiveness_k3_subset_1, axiom,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.40/2.61  thf('4', plain,
% 2.40/2.61      (![X67 : $i, X68 : $i]:
% 2.40/2.61         (((k3_subset_1 @ X68 @ (k3_subset_1 @ X68 @ X67)) = (X67))
% 2.40/2.61          | ~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ X68)))),
% 2.40/2.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.40/2.61  thf('5', plain,
% 2.40/2.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)) = (sk_B))),
% 2.40/2.61      inference('sup-', [status(thm)], ['3', '4'])).
% 2.40/2.61  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf('7', plain,
% 2.40/2.61      (![X60 : $i, X61 : $i]:
% 2.40/2.61         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 2.40/2.61          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 2.40/2.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.40/2.61  thf('8', plain,
% 2.40/2.61      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.40/2.61      inference('sup-', [status(thm)], ['6', '7'])).
% 2.40/2.61  thf(t48_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.40/2.61  thf('9', plain,
% 2.40/2.61      (![X28 : $i, X29 : $i]:
% 2.40/2.61         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 2.40/2.61           = (k3_xboole_0 @ X28 @ X29))),
% 2.40/2.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.40/2.61  thf('10', plain,
% 2.40/2.61      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 2.40/2.61         = (k3_xboole_0 @ sk_A @ sk_B))),
% 2.40/2.61      inference('sup+', [status(thm)], ['8', '9'])).
% 2.40/2.61  thf(commutativity_k3_xboole_0, axiom,
% 2.40/2.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.40/2.61  thf('11', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.40/2.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.40/2.61  thf('12', plain,
% 2.40/2.61      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 2.40/2.61         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.40/2.61      inference('demod', [status(thm)], ['10', '11'])).
% 2.40/2.61  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf(dt_k3_subset_1, axiom,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.40/2.61  thf('14', plain,
% 2.40/2.61      (![X62 : $i, X63 : $i]:
% 2.40/2.61         ((m1_subset_1 @ (k3_subset_1 @ X62 @ X63) @ (k1_zfmisc_1 @ X62))
% 2.40/2.61          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ X62)))),
% 2.40/2.61      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.40/2.61  thf('15', plain,
% 2.40/2.61      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.61      inference('sup-', [status(thm)], ['13', '14'])).
% 2.40/2.61  thf('16', plain,
% 2.40/2.61      (![X60 : $i, X61 : $i]:
% 2.40/2.61         (((k3_subset_1 @ X60 @ X61) = (k4_xboole_0 @ X60 @ X61))
% 2.40/2.61          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ X60)))),
% 2.40/2.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.40/2.61  thf('17', plain,
% 2.40/2.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 2.40/2.61         = (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B)))),
% 2.40/2.61      inference('sup-', [status(thm)], ['15', '16'])).
% 2.40/2.61  thf('18', plain,
% 2.40/2.61      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B))
% 2.40/2.61         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.40/2.61      inference('sup+', [status(thm)], ['12', '17'])).
% 2.40/2.61  thf('19', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.40/2.61      inference('sup+', [status(thm)], ['5', '18'])).
% 2.40/2.61  thf(t49_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i,C:$i]:
% 2.40/2.61     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.40/2.61       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 2.40/2.61  thf('20', plain,
% 2.40/2.61      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.61         ((k3_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X32))
% 2.40/2.61           = (k4_xboole_0 @ (k3_xboole_0 @ X30 @ X31) @ X32))),
% 2.40/2.61      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.40/2.61  thf('21', plain,
% 2.40/2.61      (![X0 : $i]:
% 2.40/2.61         ((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 2.40/2.61           = (k4_xboole_0 @ sk_B @ X0))),
% 2.40/2.61      inference('sup+', [status(thm)], ['19', '20'])).
% 2.40/2.61  thf('22', plain,
% 2.40/2.61      (((k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))
% 2.40/2.61         = (k4_xboole_0 @ sk_B @ sk_C_2))),
% 2.40/2.61      inference('sup+', [status(thm)], ['2', '21'])).
% 2.40/2.61  thf('23', plain,
% 2.40/2.61      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_2)
% 2.40/2.61         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf('24', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf(redefinition_k7_subset_1, axiom,
% 2.40/2.61    (![A:$i,B:$i,C:$i]:
% 2.40/2.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.61       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.40/2.61  thf('25', plain,
% 2.40/2.61      (![X69 : $i, X70 : $i, X71 : $i]:
% 2.40/2.61         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ X70))
% 2.40/2.61          | ((k7_subset_1 @ X70 @ X69 @ X71) = (k4_xboole_0 @ X69 @ X71)))),
% 2.40/2.61      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.40/2.61  thf('26', plain,
% 2.40/2.61      (![X0 : $i]:
% 2.40/2.61         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 2.40/2.61      inference('sup-', [status(thm)], ['24', '25'])).
% 2.40/2.61  thf('27', plain,
% 2.40/2.61      (((k4_xboole_0 @ sk_B @ sk_C_2)
% 2.40/2.61         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 2.40/2.62      inference('demod', [status(thm)], ['23', '26'])).
% 2.40/2.62  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.62  thf(commutativity_k9_subset_1, axiom,
% 2.40/2.62    (![A:$i,B:$i,C:$i]:
% 2.40/2.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 2.40/2.62  thf('29', plain,
% 2.40/2.62      (![X57 : $i, X58 : $i, X59 : $i]:
% 2.40/2.62         (((k9_subset_1 @ X57 @ X59 @ X58) = (k9_subset_1 @ X57 @ X58 @ X59))
% 2.40/2.62          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ X57)))),
% 2.40/2.62      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 2.40/2.62  thf('30', plain,
% 2.40/2.62      (![X0 : $i]:
% 2.40/2.62         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 2.40/2.62      inference('sup-', [status(thm)], ['28', '29'])).
% 2.40/2.62  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.62  thf(redefinition_k9_subset_1, axiom,
% 2.40/2.62    (![A:$i,B:$i,C:$i]:
% 2.40/2.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.40/2.62  thf('32', plain,
% 2.40/2.62      (![X72 : $i, X73 : $i, X74 : $i]:
% 2.40/2.62         (((k9_subset_1 @ X74 @ X72 @ X73) = (k3_xboole_0 @ X72 @ X73))
% 2.40/2.62          | ~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ X74)))),
% 2.40/2.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.40/2.62  thf('33', plain,
% 2.40/2.62      (![X0 : $i]:
% 2.40/2.62         ((k9_subset_1 @ sk_A @ X0 @ sk_B) = (k3_xboole_0 @ X0 @ sk_B))),
% 2.40/2.62      inference('sup-', [status(thm)], ['31', '32'])).
% 2.40/2.62  thf('34', plain,
% 2.40/2.62      (![X0 : $i]:
% 2.40/2.62         ((k3_xboole_0 @ X0 @ sk_B) = (k9_subset_1 @ sk_A @ sk_B @ X0))),
% 2.40/2.62      inference('demod', [status(thm)], ['30', '33'])).
% 2.40/2.62  thf('35', plain,
% 2.40/2.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.40/2.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.40/2.62  thf('36', plain,
% 2.40/2.62      (((k4_xboole_0 @ sk_B @ sk_C_2)
% 2.40/2.62         != (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 2.40/2.62      inference('demod', [status(thm)], ['27', '34', '35'])).
% 2.40/2.62  thf('37', plain, ($false),
% 2.40/2.62      inference('simplify_reflect-', [status(thm)], ['22', '36'])).
% 2.40/2.62  
% 2.40/2.62  % SZS output end Refutation
% 2.40/2.62  
% 2.40/2.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Djpb7SGxZ9

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:42 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  407 ( 551 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D @ X9 @ X10 @ X11 ) @ X9 )
      | ( r2_hidden @ ( sk_E @ X9 @ X10 @ X11 ) @ X10 )
      | ( X9
        = ( k10_relat_1 @ X11 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X26 @ X24 ) @ X26 ) @ X24 )
      | ( X25
       != ( k2_relat_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('3',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X26 @ X24 ) @ X26 ) @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ k1_xboole_0 ) @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t171_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t171_relat_1])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['7','12','13'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X0 @ k1_xboole_0 ) @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X19 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X21 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','11'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k1_xboole_0
        = ( k10_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ( k10_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Djpb7SGxZ9
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:38:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.52/2.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.52/2.76  % Solved by: fo/fo7.sh
% 2.52/2.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.52/2.76  % done 468 iterations in 2.293s
% 2.52/2.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.52/2.76  % SZS output start Refutation
% 2.52/2.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.52/2.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.52/2.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.52/2.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.52/2.76  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.52/2.76  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.52/2.76  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 2.52/2.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.52/2.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.52/2.76  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.52/2.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.52/2.76  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 2.52/2.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.52/2.76  thf(sk_A_type, type, sk_A: $i).
% 2.52/2.76  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.52/2.76  thf(d14_relat_1, axiom,
% 2.52/2.76    (![A:$i]:
% 2.52/2.76     ( ( v1_relat_1 @ A ) =>
% 2.52/2.76       ( ![B:$i,C:$i]:
% 2.52/2.76         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 2.52/2.76           ( ![D:$i]:
% 2.52/2.76             ( ( r2_hidden @ D @ C ) <=>
% 2.52/2.76               ( ?[E:$i]:
% 2.52/2.76                 ( ( r2_hidden @ E @ B ) & 
% 2.52/2.76                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 2.52/2.76  thf('0', plain,
% 2.52/2.76      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.52/2.76         ((r2_hidden @ (sk_D @ X9 @ X10 @ X11) @ X9)
% 2.52/2.76          | (r2_hidden @ (sk_E @ X9 @ X10 @ X11) @ X10)
% 2.52/2.76          | ((X9) = (k10_relat_1 @ X11 @ X10))
% 2.52/2.76          | ~ (v1_relat_1 @ X11))),
% 2.52/2.76      inference('cnf', [status(esa)], [d14_relat_1])).
% 2.52/2.76  thf(t60_relat_1, axiom,
% 2.52/2.76    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 2.52/2.76     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.52/2.76  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.52/2.76      inference('cnf', [status(esa)], [t60_relat_1])).
% 2.52/2.76  thf(d5_relat_1, axiom,
% 2.52/2.76    (![A:$i,B:$i]:
% 2.52/2.76     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.52/2.76       ( ![C:$i]:
% 2.52/2.76         ( ( r2_hidden @ C @ B ) <=>
% 2.52/2.76           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 2.52/2.76  thf('2', plain,
% 2.52/2.76      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.52/2.76         (~ (r2_hidden @ X26 @ X25)
% 2.52/2.76          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X26 @ X24) @ X26) @ X24)
% 2.52/2.76          | ((X25) != (k2_relat_1 @ X24)))),
% 2.52/2.76      inference('cnf', [status(esa)], [d5_relat_1])).
% 2.52/2.76  thf('3', plain,
% 2.52/2.76      (![X24 : $i, X26 : $i]:
% 2.52/2.76         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X26 @ X24) @ X26) @ X24)
% 2.52/2.76          | ~ (r2_hidden @ X26 @ (k2_relat_1 @ X24)))),
% 2.52/2.76      inference('simplify', [status(thm)], ['2'])).
% 2.52/2.76  thf('4', plain,
% 2.52/2.76      (![X0 : $i]:
% 2.52/2.76         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 2.52/2.76          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X0 @ k1_xboole_0) @ X0) @ 
% 2.52/2.76             k1_xboole_0))),
% 2.52/2.76      inference('sup-', [status(thm)], ['1', '3'])).
% 2.52/2.76  thf('5', plain,
% 2.52/2.76      (![X0 : $i, X1 : $i]:
% 2.52/2.76         (~ (v1_relat_1 @ X0)
% 2.52/2.76          | ((k1_xboole_0) = (k10_relat_1 @ X0 @ X1))
% 2.52/2.76          | (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X1)
% 2.52/2.76          | (r2_hidden @ 
% 2.52/2.76             (k4_tarski @ 
% 2.52/2.76              (sk_D_3 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 2.52/2.76              (sk_D @ k1_xboole_0 @ X1 @ X0)) @ 
% 2.52/2.76             k1_xboole_0))),
% 2.52/2.76      inference('sup-', [status(thm)], ['0', '4'])).
% 2.52/2.76  thf(d3_relat_1, axiom,
% 2.52/2.76    (![A:$i]:
% 2.52/2.76     ( ( v1_relat_1 @ A ) =>
% 2.52/2.76       ( ![B:$i]:
% 2.52/2.76         ( ( r1_tarski @ A @ B ) <=>
% 2.52/2.76           ( ![C:$i,D:$i]:
% 2.52/2.76             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 2.52/2.76               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 2.52/2.76  thf('6', plain,
% 2.52/2.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.52/2.76         (~ (r1_tarski @ X18 @ X19)
% 2.52/2.76          | (r2_hidden @ (k4_tarski @ X20 @ X21) @ X19)
% 2.52/2.76          | ~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X18)
% 2.52/2.76          | ~ (v1_relat_1 @ X18))),
% 2.52/2.76      inference('cnf', [status(esa)], [d3_relat_1])).
% 2.52/2.76  thf('7', plain,
% 2.52/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.76         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X1)
% 2.52/2.76          | ((k1_xboole_0) = (k10_relat_1 @ X0 @ X1))
% 2.52/2.76          | ~ (v1_relat_1 @ X0)
% 2.52/2.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.52/2.76          | (r2_hidden @ 
% 2.52/2.76             (k4_tarski @ 
% 2.52/2.76              (sk_D_3 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 2.52/2.76              (sk_D @ k1_xboole_0 @ X1 @ X0)) @ 
% 2.52/2.76             X2)
% 2.52/2.76          | ~ (r1_tarski @ k1_xboole_0 @ X2))),
% 2.52/2.76      inference('sup-', [status(thm)], ['5', '6'])).
% 2.52/2.76  thf(t171_relat_1, conjecture,
% 2.52/2.76    (![A:$i]:
% 2.52/2.76     ( ( v1_relat_1 @ A ) =>
% 2.52/2.76       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 2.52/2.76  thf(zf_stmt_0, negated_conjecture,
% 2.52/2.76    (~( ![A:$i]:
% 2.52/2.76        ( ( v1_relat_1 @ A ) =>
% 2.52/2.76          ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 2.52/2.76    inference('cnf.neg', [status(esa)], [t171_relat_1])).
% 2.52/2.76  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 2.52/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.76  thf(t4_subset_1, axiom,
% 2.52/2.76    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.52/2.76  thf('9', plain,
% 2.52/2.76      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 2.52/2.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.52/2.76  thf(cc2_relat_1, axiom,
% 2.52/2.76    (![A:$i]:
% 2.52/2.76     ( ( v1_relat_1 @ A ) =>
% 2.52/2.76       ( ![B:$i]:
% 2.52/2.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.52/2.76  thf('10', plain,
% 2.52/2.76      (![X7 : $i, X8 : $i]:
% 2.52/2.76         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.52/2.76          | (v1_relat_1 @ X7)
% 2.52/2.76          | ~ (v1_relat_1 @ X8))),
% 2.52/2.76      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.52/2.76  thf('11', plain,
% 2.52/2.76      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 2.52/2.76      inference('sup-', [status(thm)], ['9', '10'])).
% 2.52/2.76  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.52/2.76      inference('sup-', [status(thm)], ['8', '11'])).
% 2.52/2.76  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.52/2.76  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.52/2.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.52/2.76  thf('14', plain,
% 2.52/2.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.76         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X1)
% 2.52/2.76          | ((k1_xboole_0) = (k10_relat_1 @ X0 @ X1))
% 2.52/2.76          | ~ (v1_relat_1 @ X0)
% 2.52/2.76          | (r2_hidden @ 
% 2.52/2.76             (k4_tarski @ 
% 2.52/2.76              (sk_D_3 @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0) @ 
% 2.52/2.76              (sk_D @ k1_xboole_0 @ X1 @ X0)) @ 
% 2.52/2.76             X2))),
% 2.52/2.76      inference('demod', [status(thm)], ['7', '12', '13'])).
% 2.52/2.76  thf(t152_zfmisc_1, axiom,
% 2.52/2.76    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.52/2.76  thf('15', plain,
% 2.52/2.76      (![X1 : $i, X2 : $i]: ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 2.52/2.76      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.52/2.76  thf('16', plain,
% 2.52/2.76      (![X1 : $i, X2 : $i]:
% 2.52/2.76         (~ (v1_relat_1 @ X1)
% 2.52/2.76          | ((k1_xboole_0) = (k10_relat_1 @ X1 @ X2))
% 2.52/2.76          | (r2_hidden @ (sk_E @ k1_xboole_0 @ X2 @ X1) @ X2))),
% 2.52/2.76      inference('sup-', [status(thm)], ['14', '15'])).
% 2.52/2.76  thf('17', plain,
% 2.52/2.76      (![X0 : $i]:
% 2.52/2.76         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 2.52/2.76          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X0 @ k1_xboole_0) @ X0) @ 
% 2.52/2.76             k1_xboole_0))),
% 2.52/2.76      inference('sup-', [status(thm)], ['1', '3'])).
% 2.52/2.76  thf('18', plain,
% 2.52/2.76      (![X0 : $i]:
% 2.52/2.76         (((k1_xboole_0) = (k10_relat_1 @ X0 @ k1_xboole_0))
% 2.52/2.76          | ~ (v1_relat_1 @ X0)
% 2.52/2.76          | (r2_hidden @ 
% 2.52/2.76             (k4_tarski @ 
% 2.52/2.76              (sk_D_3 @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0) @ 
% 2.52/2.76              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 2.52/2.76             k1_xboole_0))),
% 2.52/2.76      inference('sup-', [status(thm)], ['16', '17'])).
% 2.52/2.76  thf('19', plain,
% 2.52/2.76      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.52/2.76         (~ (r1_tarski @ X18 @ X19)
% 2.52/2.76          | (r2_hidden @ (k4_tarski @ X20 @ X21) @ X19)
% 2.52/2.76          | ~ (r2_hidden @ (k4_tarski @ X20 @ X21) @ X18)
% 2.52/2.76          | ~ (v1_relat_1 @ X18))),
% 2.52/2.76      inference('cnf', [status(esa)], [d3_relat_1])).
% 2.52/2.76  thf('20', plain,
% 2.52/2.76      (![X0 : $i, X1 : $i]:
% 2.52/2.76         (~ (v1_relat_1 @ X0)
% 2.52/2.76          | ((k1_xboole_0) = (k10_relat_1 @ X0 @ k1_xboole_0))
% 2.52/2.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 2.52/2.76          | (r2_hidden @ 
% 2.52/2.76             (k4_tarski @ 
% 2.52/2.76              (sk_D_3 @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0) @ 
% 2.52/2.76              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 2.52/2.76             X1)
% 2.52/2.76          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 2.52/2.76      inference('sup-', [status(thm)], ['18', '19'])).
% 2.52/2.76  thf('21', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.52/2.76      inference('sup-', [status(thm)], ['8', '11'])).
% 2.52/2.76  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.52/2.76      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.52/2.76  thf('23', plain,
% 2.52/2.76      (![X0 : $i, X1 : $i]:
% 2.52/2.76         (~ (v1_relat_1 @ X0)
% 2.52/2.76          | ((k1_xboole_0) = (k10_relat_1 @ X0 @ k1_xboole_0))
% 2.52/2.76          | (r2_hidden @ 
% 2.52/2.76             (k4_tarski @ 
% 2.52/2.76              (sk_D_3 @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0) @ 
% 2.52/2.76              (sk_E @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 2.52/2.76             X1))),
% 2.52/2.76      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.52/2.76  thf('24', plain,
% 2.52/2.76      (![X1 : $i, X2 : $i]: ~ (r2_hidden @ X1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 2.52/2.76      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.52/2.76  thf('25', plain,
% 2.52/2.76      (![X1 : $i]:
% 2.52/2.76         (((k1_xboole_0) = (k10_relat_1 @ X1 @ k1_xboole_0))
% 2.52/2.76          | ~ (v1_relat_1 @ X1))),
% 2.52/2.76      inference('sup-', [status(thm)], ['23', '24'])).
% 2.52/2.76  thf('26', plain, (((k10_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 2.52/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.76  thf('27', plain,
% 2.52/2.76      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 2.52/2.76      inference('sup-', [status(thm)], ['25', '26'])).
% 2.52/2.76  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 2.52/2.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.76  thf('29', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 2.52/2.76      inference('demod', [status(thm)], ['27', '28'])).
% 2.52/2.76  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 2.52/2.76  
% 2.52/2.76  % SZS output end Refutation
% 2.52/2.76  
% 2.52/2.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

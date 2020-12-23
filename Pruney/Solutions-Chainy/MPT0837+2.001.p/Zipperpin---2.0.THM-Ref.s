%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PdCrTDWRYz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:54 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 159 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  441 (1924 expanded)
%              Number of equality atoms :    7 (  25 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_7_type,type,(
    sk_C_7: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_8_type,type,(
    sk_D_8: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_B_6_type,type,(
    sk_B_6: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 )
    | ( r2_hidden @ sk_D_8 @ ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_8 @ ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 ) )
   <= ( r2_hidden @ sk_D_8 @ ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_6 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X104: $i,X105: $i,X106: $i] :
      ( ( ( k2_relset_1 @ X105 @ X106 @ X104 )
        = ( k2_relat_1 @ X104 ) )
      | ~ ( m1_subset_1 @ X104 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X105 @ X106 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 )
    = ( k2_relat_1 @ sk_C_7 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_8 @ ( k2_relat_1 @ sk_C_7 ) )
   <= ( r2_hidden @ sk_D_8 @ ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    ! [X123: $i] :
      ( ~ ( m1_subset_1 @ X123 @ sk_B_6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X123 @ sk_D_8 ) @ sk_C_7 )
      | ~ ( r2_hidden @ sk_D_8 @ ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 )
    = ( k2_relat_1 @ sk_C_7 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('9',plain,(
    ! [X123: $i] :
      ( ~ ( m1_subset_1 @ X123 @ sk_B_6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X123 @ sk_D_8 ) @ sk_C_7 )
      | ~ ( r2_hidden @ sk_D_8 @ ( k2_relat_1 @ sk_C_7 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('10',plain,(
    ! [X61: $i,X62: $i,X63: $i,X64: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X61 @ X62 ) @ X63 )
      | ( r2_hidden @ X62 @ X64 )
      | ( X64
       != ( k2_relat_1 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('11',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( r2_hidden @ X62 @ ( k2_relat_1 @ X63 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X61 @ X62 ) @ X63 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X123: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X123 @ sk_D_8 ) @ sk_C_7 )
      | ~ ( m1_subset_1 @ X123 @ sk_B_6 ) ) ),
    inference(clc,[status(thm)],['9','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_E_2 @ sk_B_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_6 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_6 @ sk_A_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_7 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ ( k2_zfmisc_1 @ sk_B_6 @ sk_A_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('20',plain,
    ( ( r2_hidden @ sk_E_2 @ sk_B_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('21',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_E_2 @ sk_B_6 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_D_8 @ ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 ) )
    | ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_8 ) @ sk_C_7 ) ),
    inference(split,[status(esa)],['0'])).

thf('25',plain,(
    r2_hidden @ sk_D_8 @ ( k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7 ) ),
    inference('sat_resolution*',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_D_8 @ ( k2_relat_1 @ sk_C_7 ) ),
    inference(simpl_trail,[status(thm)],['5','25'])).

thf('27',plain,(
    ! [X63: $i,X64: $i,X65: $i] :
      ( ~ ( r2_hidden @ X65 @ X64 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X65 @ X63 ) @ X65 ) @ X63 )
      | ( X64
       != ( k2_relat_1 @ X63 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('28',plain,(
    ! [X63: $i,X65: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X65 @ X63 ) @ X65 ) @ X63 )
      | ~ ( r2_hidden @ X65 @ ( k2_relat_1 @ X63 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_8 @ sk_C_7 ) @ sk_D_8 ) @ sk_C_7 ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X123: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X123 @ sk_D_8 ) @ sk_C_7 )
      | ~ ( m1_subset_1 @ X123 @ sk_B_6 ) ) ),
    inference(clc,[status(thm)],['9','11'])).

thf('31',plain,(
    ~ ( m1_subset_1 @ ( sk_D_3 @ sk_D_8 @ sk_C_7 ) @ sk_B_6 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_8 @ sk_C_7 ) @ sk_D_8 ) @ sk_C_7 ),
    inference('sup-',[status(thm)],['26','28'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_6 @ sk_A_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_7 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('34',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_8 @ sk_C_7 ) @ sk_D_8 ) @ ( k2_zfmisc_1 @ sk_B_6 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('36',plain,(
    r2_hidden @ ( sk_D_3 @ sk_D_8 @ sk_C_7 ) @ sk_B_6 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X38: $i,X39: $i] :
      ( ( m1_subset_1 @ X38 @ X39 )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('38',plain,(
    m1_subset_1 @ ( sk_D_3 @ sk_D_8 @ sk_C_7 ) @ sk_B_6 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['31','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PdCrTDWRYz
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.14/1.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.14/1.31  % Solved by: fo/fo7.sh
% 1.14/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.31  % done 2383 iterations in 0.862s
% 1.14/1.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.14/1.31  % SZS output start Refutation
% 1.14/1.31  thf(sk_C_7_type, type, sk_C_7: $i).
% 1.14/1.31  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.14/1.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.14/1.31  thf(sk_D_8_type, type, sk_D_8: $i).
% 1.14/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.31  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.14/1.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.14/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.31  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 1.14/1.31  thf(sk_E_2_type, type, sk_E_2: $i).
% 1.14/1.31  thf(sk_B_6_type, type, sk_B_6: $i).
% 1.14/1.31  thf(sk_A_1_type, type, sk_A_1: $i).
% 1.14/1.31  thf(t48_relset_1, conjecture,
% 1.14/1.31    (![A:$i]:
% 1.14/1.31     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.31       ( ![B:$i]:
% 1.14/1.31         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.14/1.31           ( ![C:$i]:
% 1.14/1.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.14/1.31               ( ![D:$i]:
% 1.14/1.31                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 1.14/1.31                   ( ?[E:$i]:
% 1.14/1.31                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 1.14/1.31                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 1.14/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.31    (~( ![A:$i]:
% 1.14/1.31        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.31          ( ![B:$i]:
% 1.14/1.31            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.14/1.31              ( ![C:$i]:
% 1.14/1.31                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.14/1.31                  ( ![D:$i]:
% 1.14/1.31                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 1.14/1.31                      ( ?[E:$i]:
% 1.14/1.31                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 1.14/1.31                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 1.14/1.31    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 1.14/1.31  thf('0', plain,
% 1.14/1.31      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7)
% 1.14/1.31        | (r2_hidden @ sk_D_8 @ (k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7)))),
% 1.14/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.31  thf('1', plain,
% 1.14/1.31      (((r2_hidden @ sk_D_8 @ (k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7)))
% 1.14/1.31         <= (((r2_hidden @ sk_D_8 @ (k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7))))),
% 1.14/1.31      inference('split', [status(esa)], ['0'])).
% 1.14/1.31  thf('2', plain,
% 1.14/1.31      ((m1_subset_1 @ sk_C_7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_6 @ sk_A_1)))),
% 1.14/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.31  thf(redefinition_k2_relset_1, axiom,
% 1.14/1.31    (![A:$i,B:$i,C:$i]:
% 1.14/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.31       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.14/1.31  thf('3', plain,
% 1.14/1.31      (![X104 : $i, X105 : $i, X106 : $i]:
% 1.14/1.31         (((k2_relset_1 @ X105 @ X106 @ X104) = (k2_relat_1 @ X104))
% 1.14/1.31          | ~ (m1_subset_1 @ X104 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X105 @ X106))))),
% 1.14/1.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.14/1.31  thf('4', plain,
% 1.14/1.31      (((k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7) = (k2_relat_1 @ sk_C_7))),
% 1.14/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.14/1.31  thf('5', plain,
% 1.14/1.31      (((r2_hidden @ sk_D_8 @ (k2_relat_1 @ sk_C_7)))
% 1.14/1.31         <= (((r2_hidden @ sk_D_8 @ (k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7))))),
% 1.14/1.31      inference('demod', [status(thm)], ['1', '4'])).
% 1.14/1.31  thf('6', plain,
% 1.14/1.31      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7))
% 1.14/1.31         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7)))),
% 1.14/1.31      inference('split', [status(esa)], ['0'])).
% 1.14/1.31  thf('7', plain,
% 1.14/1.31      (![X123 : $i]:
% 1.14/1.31         (~ (m1_subset_1 @ X123 @ sk_B_6)
% 1.14/1.31          | ~ (r2_hidden @ (k4_tarski @ X123 @ sk_D_8) @ sk_C_7)
% 1.14/1.31          | ~ (r2_hidden @ sk_D_8 @ (k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7)))),
% 1.14/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.31  thf('8', plain,
% 1.14/1.31      (((k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7) = (k2_relat_1 @ sk_C_7))),
% 1.14/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.14/1.31  thf('9', plain,
% 1.14/1.31      (![X123 : $i]:
% 1.14/1.31         (~ (m1_subset_1 @ X123 @ sk_B_6)
% 1.14/1.31          | ~ (r2_hidden @ (k4_tarski @ X123 @ sk_D_8) @ sk_C_7)
% 1.14/1.31          | ~ (r2_hidden @ sk_D_8 @ (k2_relat_1 @ sk_C_7)))),
% 1.14/1.31      inference('demod', [status(thm)], ['7', '8'])).
% 1.14/1.31  thf(d5_relat_1, axiom,
% 1.14/1.31    (![A:$i,B:$i]:
% 1.14/1.31     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.14/1.31       ( ![C:$i]:
% 1.14/1.31         ( ( r2_hidden @ C @ B ) <=>
% 1.14/1.31           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.14/1.31  thf('10', plain,
% 1.14/1.31      (![X61 : $i, X62 : $i, X63 : $i, X64 : $i]:
% 1.14/1.31         (~ (r2_hidden @ (k4_tarski @ X61 @ X62) @ X63)
% 1.14/1.31          | (r2_hidden @ X62 @ X64)
% 1.14/1.31          | ((X64) != (k2_relat_1 @ X63)))),
% 1.14/1.31      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.14/1.31  thf('11', plain,
% 1.14/1.31      (![X61 : $i, X62 : $i, X63 : $i]:
% 1.14/1.31         ((r2_hidden @ X62 @ (k2_relat_1 @ X63))
% 1.14/1.31          | ~ (r2_hidden @ (k4_tarski @ X61 @ X62) @ X63))),
% 1.14/1.31      inference('simplify', [status(thm)], ['10'])).
% 1.14/1.31  thf('12', plain,
% 1.14/1.31      (![X123 : $i]:
% 1.14/1.31         (~ (r2_hidden @ (k4_tarski @ X123 @ sk_D_8) @ sk_C_7)
% 1.14/1.31          | ~ (m1_subset_1 @ X123 @ sk_B_6))),
% 1.14/1.31      inference('clc', [status(thm)], ['9', '11'])).
% 1.14/1.31  thf('13', plain,
% 1.14/1.31      ((~ (m1_subset_1 @ sk_E_2 @ sk_B_6))
% 1.14/1.31         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7)))),
% 1.14/1.31      inference('sup-', [status(thm)], ['6', '12'])).
% 1.14/1.31  thf('14', plain,
% 1.14/1.31      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7))
% 1.14/1.31         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7)))),
% 1.14/1.31      inference('split', [status(esa)], ['0'])).
% 1.14/1.31  thf('15', plain,
% 1.14/1.31      ((m1_subset_1 @ sk_C_7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_6 @ sk_A_1)))),
% 1.14/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.31  thf(l3_subset_1, axiom,
% 1.14/1.31    (![A:$i,B:$i]:
% 1.14/1.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.14/1.31       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.14/1.31  thf('16', plain,
% 1.14/1.31      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.14/1.31         (~ (r2_hidden @ X27 @ X28)
% 1.14/1.31          | (r2_hidden @ X27 @ X29)
% 1.14/1.31          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 1.14/1.31      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.14/1.31  thf('17', plain,
% 1.14/1.31      (![X0 : $i]:
% 1.14/1.31         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_6 @ sk_A_1))
% 1.14/1.31          | ~ (r2_hidden @ X0 @ sk_C_7))),
% 1.14/1.31      inference('sup-', [status(thm)], ['15', '16'])).
% 1.14/1.31  thf('18', plain,
% 1.14/1.31      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ 
% 1.14/1.31         (k2_zfmisc_1 @ sk_B_6 @ sk_A_1)))
% 1.14/1.31         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7)))),
% 1.14/1.31      inference('sup-', [status(thm)], ['14', '17'])).
% 1.14/1.31  thf(t106_zfmisc_1, axiom,
% 1.14/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.31     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 1.14/1.31       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 1.14/1.31  thf('19', plain,
% 1.14/1.31      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.14/1.31         ((r2_hidden @ X10 @ X11)
% 1.14/1.31          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 1.14/1.31      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.14/1.31  thf('20', plain,
% 1.14/1.31      (((r2_hidden @ sk_E_2 @ sk_B_6))
% 1.14/1.31         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7)))),
% 1.14/1.31      inference('sup-', [status(thm)], ['18', '19'])).
% 1.14/1.31  thf(t1_subset, axiom,
% 1.14/1.31    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.14/1.31  thf('21', plain,
% 1.14/1.31      (![X38 : $i, X39 : $i]:
% 1.14/1.31         ((m1_subset_1 @ X38 @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 1.14/1.31      inference('cnf', [status(esa)], [t1_subset])).
% 1.14/1.31  thf('22', plain,
% 1.14/1.31      (((m1_subset_1 @ sk_E_2 @ sk_B_6))
% 1.14/1.31         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7)))),
% 1.14/1.31      inference('sup-', [status(thm)], ['20', '21'])).
% 1.14/1.31  thf('23', plain, (~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7))),
% 1.14/1.31      inference('demod', [status(thm)], ['13', '22'])).
% 1.14/1.31  thf('24', plain,
% 1.14/1.31      (((r2_hidden @ sk_D_8 @ (k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7))) | 
% 1.14/1.31       ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_8) @ sk_C_7))),
% 1.14/1.31      inference('split', [status(esa)], ['0'])).
% 1.14/1.31  thf('25', plain,
% 1.14/1.31      (((r2_hidden @ sk_D_8 @ (k2_relset_1 @ sk_B_6 @ sk_A_1 @ sk_C_7)))),
% 1.14/1.31      inference('sat_resolution*', [status(thm)], ['23', '24'])).
% 1.14/1.31  thf('26', plain, ((r2_hidden @ sk_D_8 @ (k2_relat_1 @ sk_C_7))),
% 1.14/1.31      inference('simpl_trail', [status(thm)], ['5', '25'])).
% 1.14/1.31  thf('27', plain,
% 1.14/1.31      (![X63 : $i, X64 : $i, X65 : $i]:
% 1.14/1.31         (~ (r2_hidden @ X65 @ X64)
% 1.14/1.31          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X65 @ X63) @ X65) @ X63)
% 1.14/1.31          | ((X64) != (k2_relat_1 @ X63)))),
% 1.14/1.31      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.14/1.31  thf('28', plain,
% 1.14/1.31      (![X63 : $i, X65 : $i]:
% 1.14/1.31         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X65 @ X63) @ X65) @ X63)
% 1.14/1.31          | ~ (r2_hidden @ X65 @ (k2_relat_1 @ X63)))),
% 1.14/1.31      inference('simplify', [status(thm)], ['27'])).
% 1.14/1.31  thf('29', plain,
% 1.14/1.31      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_D_8 @ sk_C_7) @ sk_D_8) @ sk_C_7)),
% 1.14/1.31      inference('sup-', [status(thm)], ['26', '28'])).
% 1.14/1.31  thf('30', plain,
% 1.14/1.31      (![X123 : $i]:
% 1.14/1.31         (~ (r2_hidden @ (k4_tarski @ X123 @ sk_D_8) @ sk_C_7)
% 1.14/1.31          | ~ (m1_subset_1 @ X123 @ sk_B_6))),
% 1.14/1.31      inference('clc', [status(thm)], ['9', '11'])).
% 1.14/1.31  thf('31', plain, (~ (m1_subset_1 @ (sk_D_3 @ sk_D_8 @ sk_C_7) @ sk_B_6)),
% 1.14/1.31      inference('sup-', [status(thm)], ['29', '30'])).
% 1.14/1.31  thf('32', plain,
% 1.14/1.31      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_D_8 @ sk_C_7) @ sk_D_8) @ sk_C_7)),
% 1.14/1.31      inference('sup-', [status(thm)], ['26', '28'])).
% 1.14/1.31  thf('33', plain,
% 1.14/1.31      (![X0 : $i]:
% 1.14/1.31         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_6 @ sk_A_1))
% 1.14/1.31          | ~ (r2_hidden @ X0 @ sk_C_7))),
% 1.14/1.31      inference('sup-', [status(thm)], ['15', '16'])).
% 1.14/1.31  thf('34', plain,
% 1.14/1.31      ((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_D_8 @ sk_C_7) @ sk_D_8) @ 
% 1.14/1.31        (k2_zfmisc_1 @ sk_B_6 @ sk_A_1))),
% 1.14/1.31      inference('sup-', [status(thm)], ['32', '33'])).
% 1.14/1.31  thf('35', plain,
% 1.14/1.31      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.14/1.31         ((r2_hidden @ X10 @ X11)
% 1.14/1.31          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 1.14/1.31      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 1.14/1.31  thf('36', plain, ((r2_hidden @ (sk_D_3 @ sk_D_8 @ sk_C_7) @ sk_B_6)),
% 1.14/1.31      inference('sup-', [status(thm)], ['34', '35'])).
% 1.14/1.31  thf('37', plain,
% 1.14/1.31      (![X38 : $i, X39 : $i]:
% 1.14/1.31         ((m1_subset_1 @ X38 @ X39) | ~ (r2_hidden @ X38 @ X39))),
% 1.14/1.31      inference('cnf', [status(esa)], [t1_subset])).
% 1.14/1.31  thf('38', plain, ((m1_subset_1 @ (sk_D_3 @ sk_D_8 @ sk_C_7) @ sk_B_6)),
% 1.14/1.31      inference('sup-', [status(thm)], ['36', '37'])).
% 1.14/1.31  thf('39', plain, ($false), inference('demod', [status(thm)], ['31', '38'])).
% 1.14/1.31  
% 1.14/1.31  % SZS output end Refutation
% 1.14/1.31  
% 1.14/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8qF1i3OueX

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:17 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   79 (  97 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  472 ( 808 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X20 @ X17 ) @ ( sk_C_1 @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k4_tarski @ ( sk_D @ X1 @ X0 ) @ ( sk_C_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('5',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('7',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X36 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['16','21'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ( X3
       != ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('27',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X36: $i] :
      ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['11','29'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','30'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X24 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['19','20'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8qF1i3OueX
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:31:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 114 iterations in 0.055s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.18/0.49  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.18/0.49  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.18/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.18/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.18/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.18/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.18/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.49  thf('0', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.18/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.49  thf(d5_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.18/0.49       ( ![C:$i]:
% 0.18/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.18/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.18/0.49  thf('1', plain,
% 0.18/0.49      (![X17 : $i, X20 : $i]:
% 0.18/0.49         (((X20) = (k2_relat_1 @ X17))
% 0.18/0.49          | (r2_hidden @ 
% 0.18/0.49             (k4_tarski @ (sk_D @ X20 @ X17) @ (sk_C_1 @ X20 @ X17)) @ X17)
% 0.18/0.49          | (r2_hidden @ (sk_C_1 @ X20 @ X17) @ X20))),
% 0.18/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.18/0.49  thf(t7_ordinal1, axiom,
% 0.18/0.49    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      (![X25 : $i, X26 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.18/0.49      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.18/0.49  thf('3', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.18/0.49          | ((X1) = (k2_relat_1 @ X0))
% 0.18/0.49          | ~ (r1_tarski @ X0 @ 
% 0.18/0.49               (k4_tarski @ (sk_D @ X1 @ X0) @ (sk_C_1 @ X1 @ X0))))),
% 0.18/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.49  thf('4', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.18/0.49          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.18/0.49  thf(t60_relat_1, axiom,
% 0.18/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.18/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.18/0.49  thf('5', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.18/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.18/0.49  thf('6', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (((X0) = (k1_xboole_0))
% 0.18/0.49          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.18/0.49      inference('demod', [status(thm)], ['4', '5'])).
% 0.18/0.49  thf(t50_relset_1, conjecture,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.18/0.49           ( ![C:$i]:
% 0.18/0.49             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.18/0.49               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.18/0.49                    ( ![D:$i]:
% 0.18/0.49                      ( ( m1_subset_1 @ D @ B ) =>
% 0.18/0.49                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.49    (~( ![A:$i]:
% 0.18/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.18/0.49          ( ![B:$i]:
% 0.18/0.49            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.18/0.49              ( ![C:$i]:
% 0.18/0.49                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.18/0.49                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.18/0.49                       ( ![D:$i]:
% 0.18/0.49                         ( ( m1_subset_1 @ D @ B ) =>
% 0.18/0.49                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.18/0.49    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.18/0.49  thf('7', plain,
% 0.18/0.49      (![X36 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X36 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_2))
% 0.18/0.49          | ~ (m1_subset_1 @ X36 @ sk_B))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('8', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(redefinition_k1_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.18/0.49  thf('9', plain,
% 0.18/0.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.18/0.49         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.18/0.49          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.18/0.49      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.18/0.49  thf('10', plain,
% 0.18/0.49      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.18/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.49  thf('11', plain,
% 0.18/0.49      (![X36 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X36 @ (k1_relat_1 @ sk_C_2))
% 0.18/0.49          | ~ (m1_subset_1 @ X36 @ sk_B))),
% 0.18/0.49      inference('demod', [status(thm)], ['7', '10'])).
% 0.18/0.49  thf('12', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(cc2_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.18/0.49  thf('13', plain,
% 0.18/0.49      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.18/0.49         ((v4_relat_1 @ X27 @ X28)
% 0.18/0.49          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.18/0.49  thf('14', plain, ((v4_relat_1 @ sk_C_2 @ sk_B)),
% 0.18/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.49  thf(d18_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ B ) =>
% 0.18/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.18/0.49  thf('15', plain,
% 0.18/0.49      (![X13 : $i, X14 : $i]:
% 0.18/0.49         (~ (v4_relat_1 @ X13 @ X14)
% 0.18/0.49          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.18/0.49          | ~ (v1_relat_1 @ X13))),
% 0.18/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.18/0.49  thf('16', plain,
% 0.18/0.49      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.18/0.49  thf('17', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(cc2_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ A ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.18/0.49  thf('18', plain,
% 0.18/0.49      (![X11 : $i, X12 : $i]:
% 0.18/0.49         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.18/0.49          | (v1_relat_1 @ X11)
% 0.18/0.49          | ~ (v1_relat_1 @ X12))),
% 0.18/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.18/0.49  thf('19', plain,
% 0.18/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_C_2))),
% 0.18/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.18/0.49  thf(fc6_relat_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.18/0.49  thf('20', plain,
% 0.18/0.49      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.18/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.18/0.49  thf('21', plain, ((v1_relat_1 @ sk_C_2)),
% 0.18/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.49  thf('22', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B)),
% 0.18/0.49      inference('demod', [status(thm)], ['16', '21'])).
% 0.18/0.49  thf(d1_zfmisc_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.18/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.18/0.49  thf('23', plain,
% 0.18/0.49      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.18/0.49         (~ (r1_tarski @ X1 @ X2)
% 0.18/0.49          | (r2_hidden @ X1 @ X3)
% 0.18/0.49          | ((X3) != (k1_zfmisc_1 @ X2)))),
% 0.18/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.18/0.49  thf('24', plain,
% 0.18/0.49      (![X1 : $i, X2 : $i]:
% 0.18/0.49         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X1 @ X2))),
% 0.18/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.18/0.49  thf('25', plain,
% 0.18/0.49      ((r2_hidden @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['22', '24'])).
% 0.18/0.49  thf(t1_subset, axiom,
% 0.18/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.18/0.49  thf('26', plain,
% 0.18/0.49      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.18/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.18/0.49  thf('27', plain,
% 0.18/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.18/0.49  thf(t4_subset, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.18/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.18/0.49  thf('28', plain,
% 0.18/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X8 @ X9)
% 0.18/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.18/0.49          | (m1_subset_1 @ X8 @ X10))),
% 0.18/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.18/0.49  thf('29', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((m1_subset_1 @ X0 @ sk_B)
% 0.18/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.18/0.49  thf('30', plain, (![X36 : $i]: ~ (r2_hidden @ X36 @ (k1_relat_1 @ sk_C_2))),
% 0.18/0.49      inference('clc', [status(thm)], ['11', '29'])).
% 0.18/0.49  thf('31', plain, (((k1_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['6', '30'])).
% 0.18/0.49  thf(t65_relat_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( v1_relat_1 @ A ) =>
% 0.18/0.49       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.49         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.49  thf('32', plain,
% 0.18/0.49      (![X24 : $i]:
% 0.18/0.49         (((k1_relat_1 @ X24) != (k1_xboole_0))
% 0.18/0.49          | ((k2_relat_1 @ X24) = (k1_xboole_0))
% 0.18/0.49          | ~ (v1_relat_1 @ X24))),
% 0.18/0.49      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.18/0.49  thf('33', plain,
% 0.18/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.49        | ~ (v1_relat_1 @ sk_C_2)
% 0.18/0.49        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.18/0.49  thf('34', plain, ((v1_relat_1 @ sk_C_2)),
% 0.18/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.49  thf('35', plain,
% 0.18/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.18/0.49        | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.18/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.18/0.49  thf('36', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.18/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.18/0.49  thf('37', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) != (k1_xboole_0))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('38', plain,
% 0.18/0.49      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.18/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.18/0.49  thf('39', plain,
% 0.18/0.49      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.18/0.49         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.18/0.49          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.18/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.18/0.49  thf('40', plain,
% 0.18/0.49      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.18/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.18/0.49  thf('41', plain, (((k2_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 0.18/0.49      inference('demod', [status(thm)], ['37', '40'])).
% 0.18/0.49  thf('42', plain, ($false),
% 0.18/0.49      inference('simplify_reflect-', [status(thm)], ['36', '41'])).
% 0.18/0.49  
% 0.18/0.49  % SZS output end Refutation
% 0.18/0.49  
% 0.18/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

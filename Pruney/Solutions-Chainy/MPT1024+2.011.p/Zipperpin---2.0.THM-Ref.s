%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SEe4OuOWXL

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:35 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 139 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  481 (1806 expanded)
%              Number of equality atoms :   12 (  53 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X73: $i,X74: $i,X75: $i,X76: $i] :
      ( ~ ( m1_subset_1 @ X73 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X74 @ X75 ) ) )
      | ( ( k7_relset_1 @ X74 @ X75 @ X73 @ X76 )
        = ( k9_relat_1 @ X73 @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ ( k9_relat_1 @ X43 @ X41 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X43 @ X41 @ X42 ) @ X42 ) @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( v1_relat_1 @ X61 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ~ ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','9'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('16',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( m1_subset_1 @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X91: $i] :
      ( ~ ( r2_hidden @ X91 @ sk_A )
      | ~ ( r2_hidden @ X91 @ sk_C_2 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X91 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','9'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X57 @ X59 ) @ X58 )
      | ( X59
        = ( k1_funct_1 @ X58 @ X57 ) )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ ( k9_relat_1 @ X43 @ X41 ) )
      | ( r2_hidden @ ( sk_D @ X43 @ X41 @ X42 ) @ X41 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('35',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_C_2 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['24','30','35'])).

thf('37',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','37'])).

thf('39',plain,(
    $false ),
    inference('sup-',[status(thm)],['10','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.10  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SEe4OuOWXL
% 0.10/0.31  % Computer   : n011.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 11:05:27 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.10/0.32  % Number of cores: 8
% 0.10/0.32  % Python version: Python 3.6.8
% 0.10/0.32  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 633 iterations in 0.208s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.45/0.64  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.64  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.64  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.64  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.64  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.64  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.64  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.64  thf(t115_funct_2, conjecture,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64       ( ![E:$i]:
% 0.45/0.64         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.45/0.64              ( ![F:$i]:
% 0.45/0.64                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.45/0.64                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.64            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.64          ( ![E:$i]:
% 0.45/0.64            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.45/0.64                 ( ![F:$i]:
% 0.45/0.64                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.45/0.64                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C_2))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X73 : $i, X74 : $i, X75 : $i, X76 : $i]:
% 0.45/0.64         (~ (m1_subset_1 @ X73 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X74 @ X75)))
% 0.45/0.64          | ((k7_relset_1 @ X74 @ X75 @ X73 @ X76) = (k9_relat_1 @ X73 @ X76)))),
% 0.45/0.64      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.45/0.64           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.45/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.64  thf(t143_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ C ) =>
% 0.45/0.64       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.64         ( ?[D:$i]:
% 0.45/0.64           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.64             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.64             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X42 @ (k9_relat_1 @ X43 @ X41))
% 0.45/0.64          | (r2_hidden @ (k4_tarski @ (sk_D @ X43 @ X41 @ X42) @ X42) @ X43)
% 0.45/0.64          | ~ (v1_relat_1 @ X43))),
% 0.45/0.64      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.64        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.45/0.64           sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relset_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.64       ( v1_relat_1 @ C ) ))).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (![X61 : $i, X62 : $i, X63 : $i]:
% 0.45/0.64         ((v1_relat_1 @ X61)
% 0.45/0.64          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.64  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.45/0.64        sk_D_1)),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t5_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.64          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.64  thf('12', plain,
% 0.45/0.64      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X34 @ X35)
% 0.45/0.64          | ~ (v1_xboole_0 @ X36)
% 0.45/0.64          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.45/0.64          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf('14', plain,
% 0.45/0.64      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.45/0.64        sk_D_1)),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t4_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.64       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X31 @ X32)
% 0.45/0.64          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 0.45/0.64          | (m1_subset_1 @ X31 @ X33))),
% 0.45/0.64      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.45/0.64          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.45/0.64      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      ((m1_subset_1 @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.45/0.64        (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.64  thf(t2_subset, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.64       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X29 : $i, X30 : $i]:
% 0.45/0.64         ((r2_hidden @ X29 @ X30)
% 0.45/0.64          | (v1_xboole_0 @ X30)
% 0.45/0.64          | ~ (m1_subset_1 @ X29 @ X30))),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.64  thf('20', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.45/0.64        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.45/0.64           (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.64  thf(t106_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.64     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.45/0.64       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.45/0.64         ((r2_hidden @ X10 @ X11)
% 0.45/0.64          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.45/0.64        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A))),
% 0.45/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X91 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X91 @ sk_A)
% 0.45/0.64          | ~ (r2_hidden @ X91 @ sk_C_2)
% 0.45/0.64          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X91)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.45/0.64        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E)))
% 0.45/0.64        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.64  thf('25', plain,
% 0.45/0.64      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.45/0.64        sk_D_1)),
% 0.45/0.64      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.64  thf(t8_funct_1, axiom,
% 0.45/0.64    (![A:$i,B:$i,C:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.64       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.45/0.64         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.64           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.45/0.64         (~ (r2_hidden @ (k4_tarski @ X57 @ X59) @ X58)
% 0.45/0.64          | ((X59) = (k1_funct_1 @ X58 @ X57))
% 0.45/0.64          | ~ (v1_funct_1 @ X58)
% 0.45/0.64          | ~ (v1_relat_1 @ X58))),
% 0.45/0.64      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.64  thf('27', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.64        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.64        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.64  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E)))),
% 0.45/0.64      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.45/0.64  thf('31', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.45/0.64      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.45/0.64         (~ (r2_hidden @ X42 @ (k9_relat_1 @ X43 @ X41))
% 0.45/0.64          | (r2_hidden @ (sk_D @ X43 @ X41 @ X42) @ X41)
% 0.45/0.64          | ~ (v1_relat_1 @ X43))),
% 0.45/0.64      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.64        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2))),
% 0.45/0.64      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.64  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('35', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2)),
% 0.45/0.64      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | ((sk_E) != (sk_E)))),
% 0.47/0.64      inference('demod', [status(thm)], ['24', '30', '35'])).
% 0.47/0.64  thf('37', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 0.47/0.64      inference('simplify', [status(thm)], ['36'])).
% 0.47/0.64  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D_1)),
% 0.47/0.64      inference('demod', [status(thm)], ['13', '37'])).
% 0.47/0.64  thf('39', plain, ($false), inference('sup-', [status(thm)], ['10', '38'])).
% 0.47/0.64  
% 0.47/0.64  % SZS output end Refutation
% 0.47/0.64  
% 0.47/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

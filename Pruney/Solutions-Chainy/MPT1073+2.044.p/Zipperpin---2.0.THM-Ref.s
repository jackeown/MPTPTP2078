%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lKVpVPcyUg

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 105 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  397 (1054 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X16 @ X13 ) @ ( k1_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('17',plain,(
    v4_relat_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['19','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['14','25'])).

thf('27',plain,(
    ! [X25: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('30',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k2_relat_1 @ X13 ) )
      | ( X16
        = ( k1_funct_1 @ X13 @ ( sk_D_1 @ X16 @ X13 ) ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('31',plain,(
    ! [X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k2_relat_1 @ X13 ) )
      | ( X16
        = ( k1_funct_1 @ X13 @ ( sk_D_1 @ X16 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['11','12'])).

thf('35',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lKVpVPcyUg
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:23:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 57 iterations in 0.043s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(t190_funct_2, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.49       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.20/0.49            ( ![E:$i]:
% 0.20/0.49              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.49            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.49          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.20/0.49               ( ![E:$i]:
% 0.20/0.49                 ( ( m1_subset_1 @ E @ B ) =>
% 0.20/0.49                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.49         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.20/0.49          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf(d5_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49               ( ?[D:$i]:
% 0.20/0.49                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.20/0.49                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         (((X15) != (k2_relat_1 @ X13))
% 0.20/0.49          | (r2_hidden @ (sk_D_1 @ X16 @ X13) @ (k1_relat_1 @ X13))
% 0.20/0.49          | ~ (r2_hidden @ X16 @ X15)
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X13 : $i, X16 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X13)
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.20/0.49          | (r2_hidden @ (sk_D_1 @ X16 @ X13) @ (k1_relat_1 @ X13)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.20/0.49        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_D_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.49  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.49          | (v1_relat_1 @ X6)
% 0.20/0.49          | ~ (v1_relat_1 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)) | (v1_relat_1 @ sk_D_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('13', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.49         ((v4_relat_1 @ X19 @ X20)
% 0.20/0.49          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('17', plain, ((v4_relat_1 @ sk_D_2 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(d18_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (v4_relat_1 @ X8 @ X9)
% 0.20/0.49          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.20/0.49          | ~ (v1_relat_1 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((m1_subset_1 @ (k1_relat_1 @ sk_D_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf(t4_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.49       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.49          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.49          | (m1_subset_1 @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((m1_subset_1 @ X0 @ sk_B)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X25 : $i]:
% 0.20/0.49         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X25))
% 0.20/0.49          | ~ (m1_subset_1 @ X25 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         (((X15) != (k2_relat_1 @ X13))
% 0.20/0.49          | ((X16) = (k1_funct_1 @ X13 @ (sk_D_1 @ X16 @ X13)))
% 0.20/0.49          | ~ (r2_hidden @ X16 @ X15)
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (v1_relat_1 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X13 : $i, X16 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X13)
% 0.20/0.49          | ~ (v1_funct_1 @ X13)
% 0.20/0.49          | ~ (r2_hidden @ X16 @ (k2_relat_1 @ X13))
% 0.20/0.49          | ((X16) = (k1_funct_1 @ X13 @ (sk_D_1 @ X16 @ X13))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      ((((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))
% 0.20/0.49        | ~ (v1_funct_1 @ sk_D_2)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_D_2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '31'])).
% 0.20/0.49  thf('33', plain, ((v1_funct_1 @ sk_D_2)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, ((v1_relat_1 @ sk_D_2)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.49  thf('36', plain, (((sk_A) != (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['28', '35'])).
% 0.20/0.49  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

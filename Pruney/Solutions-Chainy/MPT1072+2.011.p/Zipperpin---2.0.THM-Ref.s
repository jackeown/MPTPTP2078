%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dJ6hJjOpJT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  79 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  381 (1019 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t189_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ A @ B )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                   => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t189_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_funct_2 @ X15 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X12 ) @ ( k2_relset_1 @ X13 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X8 @ X9 @ X10 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ X9 )
      | ( ( k3_funct_2 @ X9 @ X10 @ X8 @ X11 )
        = ( k1_funct_1 @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ sk_C )
    = ( k1_funct_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dJ6hJjOpJT
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 31 iterations in 0.018s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.46  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.46  thf(t189_funct_2, conjecture,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46       ( ![B:$i]:
% 0.21/0.46         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.46           ( ![C:$i]:
% 0.21/0.46             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.46               ( ![D:$i]:
% 0.21/0.46                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.46                     ( m1_subset_1 @
% 0.21/0.46                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.46                   ( r2_hidden @
% 0.21/0.46                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.21/0.46                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]:
% 0.21/0.46        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46          ( ![B:$i]:
% 0.21/0.46            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.46              ( ![C:$i]:
% 0.21/0.46                ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.46                  ( ![D:$i]:
% 0.21/0.46                    ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.46                        ( m1_subset_1 @
% 0.21/0.46                          D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.46                      ( r2_hidden @
% 0.21/0.46                        ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.21/0.46                        ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t189_funct_2])).
% 0.21/0.46  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('1', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t2_subset, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (![X4 : $i, X5 : $i]:
% 0.21/0.46         ((r2_hidden @ X4 @ X5)
% 0.21/0.46          | (v1_xboole_0 @ X5)
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.46  thf('3', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.46  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('5', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.46      inference('clc', [status(thm)], ['3', '4'])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t6_funct_2, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.46       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.46         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.46           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X12 @ X13)
% 0.21/0.46          | ((X14) = (k1_xboole_0))
% 0.21/0.46          | ~ (v1_funct_1 @ X15)
% 0.21/0.46          | ~ (v1_funct_2 @ X15 @ X13 @ X14)
% 0.21/0.46          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.46          | (r2_hidden @ (k1_funct_1 @ X15 @ X12) @ 
% 0.21/0.46             (k2_relset_1 @ X13 @ X14 @ X15)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.46           (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D))
% 0.21/0.46          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.21/0.46          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.46          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.46          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.46           (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D))
% 0.21/0.46          | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.46          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((((sk_B_1) = (k1_xboole_0))
% 0.21/0.46        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ 
% 0.21/0.46           (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '11'])).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (~ (r2_hidden @ (k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ sk_C) @ 
% 0.21/0.46          (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('14', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.46         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.46         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.46       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10)))
% 0.21/0.46          | ~ (v1_funct_2 @ X8 @ X9 @ X10)
% 0.21/0.46          | ~ (v1_funct_1 @ X8)
% 0.21/0.46          | (v1_xboole_0 @ X9)
% 0.21/0.46          | ~ (m1_subset_1 @ X11 @ X9)
% 0.21/0.46          | ((k3_funct_2 @ X9 @ X10 @ X8 @ X11) = (k1_funct_1 @ X8 @ X11)))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.46          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.46          | (v1_xboole_0 @ sk_A)
% 0.21/0.46          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.46          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1))),
% 0.21/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.46  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('19', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('20', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.46          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.46          | (v1_xboole_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.21/0.46  thf('21', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('22', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.46          | ((k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ X0)
% 0.21/0.46              = (k1_funct_1 @ sk_D @ X0)))),
% 0.21/0.46      inference('clc', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain,
% 0.21/0.46      (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_D @ sk_C) = (k1_funct_1 @ sk_D @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['14', '22'])).
% 0.21/0.46  thf('24', plain,
% 0.21/0.46      (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ 
% 0.21/0.46          (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D))),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '23'])).
% 0.21/0.46  thf('25', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '24'])).
% 0.21/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.46  thf('26', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.46  thf(d1_xboole_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.46  thf('27', plain,
% 0.21/0.46      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.46  thf(t7_ordinal1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.46  thf('28', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]: (~ (r2_hidden @ X6 @ X7) | ~ (r1_tarski @ X7 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.46  thf('29', plain,
% 0.21/0.46      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.46  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.46      inference('sup-', [status(thm)], ['26', '29'])).
% 0.21/0.46  thf('31', plain, ($false),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '25', '30'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

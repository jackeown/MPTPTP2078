%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eTWhKgKt9M

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:56 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 146 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  497 (2130 expanded)
%              Number of equality atoms :   12 (  68 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t5_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( ( k1_relat_1 @ C )
              = A )
            & ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('3',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('4',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('9',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_C_2 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_C_2 ) @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X13 ) @ sk_B )
      | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_C_2 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['23'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X11 ) @ X12 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,
    ( $false
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
   <= ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['23'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( v1_funct_2 @ X11 @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( v1_funct_2 @ sk_C_2 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,(
    ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['34','43','44'])).

thf('46',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['31','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eTWhKgKt9M
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:15:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 99 iterations in 0.112s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(t5_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.56       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.38/0.56           ( ![D:$i]:
% 0.38/0.56             ( ( r2_hidden @ D @ A ) =>
% 0.38/0.56               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 0.38/0.56         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.56          ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.38/0.56              ( ![D:$i]:
% 0.38/0.56                ( ( r2_hidden @ D @ A ) =>
% 0.38/0.56                  ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 0.38/0.56            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t5_funct_2])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_C_2)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.38/0.56        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.38/0.56         <= (~
% 0.38/0.56             ((m1_subset_1 @ sk_C_2 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf(d3_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X1 : $i, X3 : $i]:
% 0.38/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.56  thf(d5_funct_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.56               ( ?[D:$i]:
% 0.38/0.56                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.56                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (((X7) != (k2_relat_1 @ X5))
% 0.38/0.56          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 0.38/0.56          | ~ (r2_hidden @ X8 @ X7)
% 0.38/0.56          | ~ (v1_funct_1 @ X5)
% 0.38/0.56          | ~ (v1_relat_1 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X5 : $i, X8 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X5)
% 0.38/0.56          | ~ (v1_funct_1 @ X5)
% 0.38/0.56          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 0.38/0.56          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.38/0.56          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.38/0.56              = (k1_funct_1 @ X0 @ 
% 0.38/0.56                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.56  thf('6', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X1 : $i, X3 : $i]:
% 0.38/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.38/0.56         (((X7) != (k2_relat_1 @ X5))
% 0.38/0.56          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 0.38/0.56          | ~ (r2_hidden @ X8 @ X7)
% 0.38/0.56          | ~ (v1_funct_1 @ X5)
% 0.38/0.56          | ~ (v1_relat_1 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (![X5 : $i, X8 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X5)
% 0.38/0.56          | ~ (v1_funct_1 @ X5)
% 0.38/0.56          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 0.38/0.56          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.38/0.56          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.38/0.56             (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '9'])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ 
% 0.38/0.56           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_C_2) @ sk_A)
% 0.38/0.56          | ~ (v1_relat_1 @ sk_C_2)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_C_2)
% 0.38/0.56          | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['6', '10'])).
% 0.38/0.56  thf('12', plain, ((v1_relat_1 @ sk_C_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('13', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ 
% 0.38/0.56           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_C_2) @ sk_A)
% 0.38/0.56          | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X13 : $i]:
% 0.38/0.56         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X13) @ sk_B)
% 0.38/0.56          | ~ (r2_hidden @ X13 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (k1_funct_1 @ sk_C_2 @ 
% 0.38/0.56              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_C_2)) @ 
% 0.38/0.56             sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B)
% 0.38/0.56          | ~ (v1_relat_1 @ sk_C_2)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_C_2)
% 0.38/0.56          | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.38/0.56          | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0))),
% 0.38/0.56      inference('sup+', [status(thm)], ['5', '16'])).
% 0.38/0.56  thf('18', plain, ((v1_relat_1 @ sk_C_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('19', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B)
% 0.38/0.56          | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.38/0.56          | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 0.38/0.56          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 0.38/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X1 : $i, X3 : $i]:
% 0.38/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.38/0.56        | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.38/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.56  thf(t4_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.56       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.56         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.38/0.56           ( m1_subset_1 @
% 0.38/0.56             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i]:
% 0.38/0.56         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.38/0.57          | (m1_subset_1 @ X11 @ 
% 0.38/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X11) @ X12)))
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C_2)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_C_2)
% 0.38/0.57        | (m1_subset_1 @ sk_C_2 @ 
% 0.38/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_2) @ sk_B))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain, ((v1_relat_1 @ sk_C_2)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('28', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('29', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (($false)
% 0.38/0.57         <= (~
% 0.38/0.57             ((m1_subset_1 @ sk_C_2 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['1', '30'])).
% 0.38/0.57  thf('32', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('33', plain, ((~ (v1_funct_1 @ sk_C_2)) <= (~ ((v1_funct_1 @ sk_C_2)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('34', plain, (((v1_funct_1 @ sk_C_2))),
% 0.38/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.38/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.38/0.57          | (v1_funct_2 @ X11 @ (k1_relat_1 @ X11) @ X12)
% 0.38/0.57          | ~ (v1_funct_1 @ X11)
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C_2)
% 0.38/0.57        | ~ (v1_funct_1 @ sk_C_2)
% 0.38/0.57        | (v1_funct_2 @ sk_C_2 @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('38', plain, ((v1_relat_1 @ sk_C_2)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('39', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('40', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('41', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.38/0.57      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      ((~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))
% 0.38/0.57         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('43', plain, (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (~ ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.38/0.57       ~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)) | ~ ((v1_funct_1 @ sk_C_2))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (~ ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['34', '43', '44'])).
% 0.38/0.57  thf('46', plain, ($false),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['31', '45'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

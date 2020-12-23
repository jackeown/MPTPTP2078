%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PzFt2KUZuf

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:54 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 119 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  581 (1621 expanded)
%              Number of equality atoms :    7 (  15 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t47_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) )
                    <=> ? [E: $i] :
                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                          & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('2',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('7',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X14 @ ( sk_D_1 @ X14 @ X12 ) ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('16',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('18',plain,(
    ! [X20: $i] :
      ( ~ ( m1_subset_1 @ X20 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_B )
   <= ( ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
      & ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('24',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('26',plain,
    ( ( r2_hidden @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,
    ( ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) )
   <= ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('31',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
      & ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ~ ! [X20: $i] :
          ( ~ ( m1_subset_1 @ X20 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
    | ! [X20: $i] :
        ( ~ ( m1_subset_1 @ X20 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X20 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('34',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k1_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ sk_E ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_2 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['21','32','33','34','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PzFt2KUZuf
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:00:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 139 iterations in 0.144s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.39/0.58  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.58  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(t47_relset_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58               ( ![D:$i]:
% 0.39/0.58                 ( ( m1_subset_1 @ D @ A ) =>
% 0.39/0.58                   ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.39/0.58                     ( ?[E:$i]:
% 0.39/0.58                       ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.39/0.58                         ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58                  ( ![D:$i]:
% 0.39/0.58                    ( ( m1_subset_1 @ D @ A ) =>
% 0.39/0.58                      ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ B @ C ) ) <=>
% 0.39/0.58                        ( ?[E:$i]:
% 0.39/0.58                          ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) & 
% 0.39/0.58                            ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t47_relset_1])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.58         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.39/0.58          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)
% 0.39/0.58        | (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('split', [status(esa)], ['3'])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('sup+', [status(thm)], ['2', '4'])).
% 0.39/0.58  thf(d4_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( r2_hidden @ C @ B ) <=>
% 0.39/0.58           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X14 @ X13)
% 0.39/0.58          | (r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.39/0.58          | ((X13) != (k1_relat_1 @ X12)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X12 : $i, X14 : $i]:
% 0.39/0.58         ((r2_hidden @ (k4_tarski @ X14 @ (sk_D_1 @ X14 @ X12)) @ X12)
% 0.39/0.58          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X12)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(l3_subset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.58       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X5 @ X6)
% 0.39/0.58          | (r2_hidden @ X5 @ X7)
% 0.39/0.58          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.39/0.58      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ 
% 0.39/0.58         (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.39/0.58  thf(t106_zfmisc_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.39/0.58       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((r2_hidden @ X2 @ X3)
% 0.39/0.58          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (((r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf(t1_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (((m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '7'])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X20 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1)
% 0.39/0.58          | ~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      ((![X20 : $i]:
% 0.39/0.58          (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1)))
% 0.39/0.58         <= ((![X20 : $i]:
% 0.39/0.58                (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1))))),
% 0.39/0.58      inference('split', [status(esa)], ['18'])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      ((~ (m1_subset_1 @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_B))
% 0.39/0.58         <= (((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) & 
% 0.39/0.58             (![X20 : $i]:
% 0.39/0.58                (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '19'])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.39/0.58       ~
% 0.39/0.58       (![X20 : $i]:
% 0.39/0.58          (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['16', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.39/0.58      inference('split', [status(esa)], ['3'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.39/0.58          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         ((r2_hidden @ X2 @ X3)
% 0.39/0.58          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (((r2_hidden @ sk_E @ sk_B))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (((m1_subset_1 @ sk_E @ sk_B))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.39/0.58      inference('split', [status(esa)], ['3'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      ((![X20 : $i]:
% 0.39/0.58          (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1)))
% 0.39/0.58         <= ((![X20 : $i]:
% 0.39/0.58                (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1))))),
% 0.39/0.58      inference('split', [status(esa)], ['18'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) & 
% 0.39/0.58             (![X20 : $i]:
% 0.39/0.58                (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58                 | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 0.39/0.58       ~
% 0.39/0.58       (![X20 : $i]:
% 0.39/0.58          (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '31'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))) | 
% 0.39/0.58       (![X20 : $i]:
% 0.39/0.58          (~ (m1_subset_1 @ X20 @ sk_B)
% 0.39/0.58           | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X20) @ sk_C_1)))),
% 0.39/0.58      inference('split', [status(esa)], ['18'])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 0.39/0.58       ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('split', [status(esa)], ['3'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.39/0.58      inference('split', [status(esa)], ['3'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.39/0.58         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.39/0.58          | (r2_hidden @ X10 @ X13)
% 0.39/0.58          | ((X13) != (k1_relat_1 @ X12)))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         ((r2_hidden @ X10 @ (k1_relat_1 @ X12))
% 0.39/0.58          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 0.39/0.58      inference('simplify', [status(thm)], ['36'])).
% 0.39/0.58  thf('38', plain,
% 0.39/0.58      (((r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.39/0.58         <= (((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['35', '37'])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      ((~ (r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))
% 0.39/0.58         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('split', [status(esa)], ['18'])).
% 0.39/0.58  thf('41', plain,
% 0.39/0.58      ((~ (r2_hidden @ sk_D_2 @ (k1_relat_1 @ sk_C_1)))
% 0.39/0.58         <= (~ ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (~ ((r2_hidden @ (k4_tarski @ sk_D_2 @ sk_E) @ sk_C_1)) | 
% 0.39/0.58       ((r2_hidden @ sk_D_2 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['38', '41'])).
% 0.39/0.58  thf('43', plain, ($false),
% 0.39/0.58      inference('sat_resolution*', [status(thm)],
% 0.39/0.58                ['21', '32', '33', '34', '42'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

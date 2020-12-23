%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iRG6FKz0AO

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:49 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 200 expanded)
%              Number of leaves         :   29 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  602 (2319 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X17 @ X15 ) @ ( k2_zfmisc_1 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X62: $i] :
      ( ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X62 ) @ ( k2_relat_1 @ X62 ) ) ) )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k1_relset_1 @ X52 @ X53 @ X51 )
        = ( k1_relat_1 @ X51 ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( X56
       != ( k1_relset_1 @ X56 @ X57 @ X58 ) )
      | ( v1_funct_2 @ X58 @ X56 @ X57 )
      | ~ ( zip_tseitin_5 @ X58 @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','26','27'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['18','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( zip_tseitin_4 @ X59 @ X60 )
      | ( zip_tseitin_5 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,
    ( ( zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_4 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X54: $i,X55: $i] :
      ( ( zip_tseitin_4 @ X54 @ X55 )
      | ( X54 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_4 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( sk_A
      = ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ sk_A @ X0 )
      | ( sk_A
        = ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X62: $i] :
      ( ( v1_funct_2 @ X62 @ ( k1_relat_1 @ X62 ) @ ( k2_relat_1 @ X62 ) )
      | ~ ( v1_funct_1 @ X62 )
      | ~ ( v1_relat_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
      | ( zip_tseitin_4 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
      | ( zip_tseitin_4 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('47',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_4 @ sk_A @ X0 )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','26','27'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_4 @ sk_A @ X0 ) ),
    inference(simpl_trail,[status(thm)],['47','48'])).

thf('50',plain,(
    zip_tseitin_5 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['30','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iRG6FKz0AO
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:47:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 461 iterations in 0.369s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.79  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.58/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.79  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.58/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.79  thf(t4_funct_2, conjecture,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.79       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.58/0.79         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.58/0.79           ( m1_subset_1 @
% 0.58/0.79             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i]:
% 0.58/0.79        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.58/0.79          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.58/0.79            ( ( v1_funct_1 @ B ) & 
% 0.58/0.79              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.58/0.79              ( m1_subset_1 @
% 0.58/0.79                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.58/0.79  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(t118_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( r1_tarski @ A @ B ) =>
% 0.58/0.79       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.58/0.79         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.58/0.79         (~ (r1_tarski @ X15 @ X16)
% 0.58/0.79          | (r1_tarski @ (k2_zfmisc_1 @ X17 @ X15) @ (k2_zfmisc_1 @ X17 @ X16)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)) @ 
% 0.58/0.79          (k2_zfmisc_1 @ X0 @ sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.79  thf(t3_funct_2, axiom,
% 0.58/0.79    (![A:$i]:
% 0.58/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.79       ( ( v1_funct_1 @ A ) & 
% 0.58/0.79         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.58/0.79         ( m1_subset_1 @
% 0.58/0.79           A @ 
% 0.58/0.79           ( k1_zfmisc_1 @
% 0.58/0.79             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X62 : $i]:
% 0.58/0.79         ((m1_subset_1 @ X62 @ 
% 0.58/0.79           (k1_zfmisc_1 @ 
% 0.58/0.79            (k2_zfmisc_1 @ (k1_relat_1 @ X62) @ (k2_relat_1 @ X62))))
% 0.58/0.79          | ~ (v1_funct_1 @ X62)
% 0.58/0.79          | ~ (v1_relat_1 @ X62))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.58/0.79  thf(t3_subset, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i]:
% 0.58/0.79         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         (~ (v1_relat_1 @ X0)
% 0.58/0.79          | ~ (v1_funct_1 @ X0)
% 0.58/0.79          | (r1_tarski @ X0 @ 
% 0.58/0.79             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['3', '4'])).
% 0.58/0.79  thf(t1_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.58/0.79       ( r1_tarski @ A @ C ) ))).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.58/0.79         (~ (r1_tarski @ X7 @ X8)
% 0.58/0.79          | ~ (r1_tarski @ X8 @ X9)
% 0.58/0.79          | (r1_tarski @ X7 @ X9))),
% 0.58/0.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (v1_funct_1 @ X0)
% 0.58/0.79          | ~ (v1_relat_1 @ X0)
% 0.58/0.79          | (r1_tarski @ X0 @ X1)
% 0.58/0.79          | ~ (r1_tarski @ 
% 0.58/0.79               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.58/0.79        | ~ (v1_relat_1 @ sk_B)
% 0.58/0.79        | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['2', '7'])).
% 0.58/0.79  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.58/0.79      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (![X18 : $i, X20 : $i]:
% 0.58/0.79         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.79  thf('13', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_B @ 
% 0.58/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.58/0.79         (((k1_relset_1 @ X52 @ X53 @ X51) = (k1_relat_1 @ X51))
% 0.58/0.79          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53))))),
% 0.58/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.79  thf('15', plain,
% 0.58/0.79      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.79  thf(d1_funct_2, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_1, axiom,
% 0.58/0.79    (![C:$i,B:$i,A:$i]:
% 0.58/0.79     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.58/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.58/0.79         (((X56) != (k1_relset_1 @ X56 @ X57 @ X58))
% 0.58/0.79          | (v1_funct_2 @ X58 @ X56 @ X57)
% 0.58/0.79          | ~ (zip_tseitin_5 @ X58 @ X57 @ X56))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.58/0.79        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.58/0.79        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.58/0.79        | ~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['17'])).
% 0.58/0.79  thf('19', plain,
% 0.58/0.79      ((~ (v1_funct_1 @ sk_B)
% 0.58/0.79        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.58/0.79        | ~ (m1_subset_1 @ sk_B @ 
% 0.58/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.58/0.79         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.58/0.79      inference('split', [status(esa)], ['19'])).
% 0.58/0.79  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('22', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.58/0.79      inference('split', [status(esa)], ['19'])).
% 0.58/0.79  thf('23', plain, (((v1_funct_1 @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_B @ 
% 0.58/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.79  thf('25', plain,
% 0.58/0.79      ((~ (m1_subset_1 @ sk_B @ 
% 0.58/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.58/0.79         <= (~
% 0.58/0.79             ((m1_subset_1 @ sk_B @ 
% 0.58/0.79               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.58/0.79      inference('split', [status(esa)], ['19'])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (((m1_subset_1 @ sk_B @ 
% 0.58/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.58/0.79       ~
% 0.58/0.79       ((m1_subset_1 @ sk_B @ 
% 0.58/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.58/0.79       ~ ((v1_funct_1 @ sk_B))),
% 0.58/0.79      inference('split', [status(esa)], ['19'])).
% 0.58/0.79  thf('28', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.58/0.79      inference('sat_resolution*', [status(thm)], ['23', '26', '27'])).
% 0.58/0.79  thf('29', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.58/0.79      inference('simpl_trail', [status(thm)], ['20', '28'])).
% 0.58/0.79  thf('30', plain, (~ (zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.58/0.79      inference('clc', [status(thm)], ['18', '29'])).
% 0.58/0.79  thf('31', plain,
% 0.58/0.79      ((m1_subset_1 @ sk_B @ 
% 0.58/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.79  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.58/0.79  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.58/0.79  thf(zf_stmt_4, axiom,
% 0.58/0.79    (![B:$i,A:$i]:
% 0.58/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.79       ( zip_tseitin_4 @ B @ A ) ))).
% 0.58/0.79  thf(zf_stmt_5, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.79       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.58/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.79  thf('32', plain,
% 0.58/0.79      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.58/0.79         (~ (zip_tseitin_4 @ X59 @ X60)
% 0.58/0.79          | (zip_tseitin_5 @ X61 @ X59 @ X60)
% 0.58/0.79          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59))))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.79  thf('33', plain,
% 0.58/0.79      (((zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.58/0.79        | ~ (zip_tseitin_4 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.58/0.79  thf('34', plain,
% 0.58/0.79      (![X54 : $i, X55 : $i]:
% 0.58/0.79         ((zip_tseitin_4 @ X54 @ X55) | ((X54) = (k1_xboole_0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.79  thf('35', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.58/0.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.79  thf('36', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((r1_tarski @ X0 @ X1) | (zip_tseitin_4 @ X0 @ X2))),
% 0.58/0.79      inference('sup+', [status(thm)], ['34', '35'])).
% 0.58/0.79  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(d10_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.79  thf('38', plain,
% 0.58/0.79      (![X4 : $i, X6 : $i]:
% 0.58/0.79         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.58/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.58/0.79  thf('39', plain,
% 0.58/0.79      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.58/0.79        | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['37', '38'])).
% 0.58/0.79  thf('40', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((zip_tseitin_4 @ sk_A @ X0) | ((sk_A) = (k2_relat_1 @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['36', '39'])).
% 0.58/0.79  thf('41', plain,
% 0.58/0.79      (![X62 : $i]:
% 0.58/0.79         ((v1_funct_2 @ X62 @ (k1_relat_1 @ X62) @ (k2_relat_1 @ X62))
% 0.58/0.79          | ~ (v1_funct_1 @ X62)
% 0.58/0.79          | ~ (v1_relat_1 @ X62))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.58/0.79  thf('42', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.58/0.79          | (zip_tseitin_4 @ sk_A @ X0)
% 0.58/0.79          | ~ (v1_relat_1 @ sk_B)
% 0.58/0.79          | ~ (v1_funct_1 @ sk_B))),
% 0.58/0.79      inference('sup+', [status(thm)], ['40', '41'])).
% 0.58/0.79  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('45', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.58/0.79          | (zip_tseitin_4 @ sk_A @ X0))),
% 0.58/0.79      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.58/0.79  thf('46', plain,
% 0.58/0.79      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.58/0.79         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.58/0.79      inference('split', [status(esa)], ['19'])).
% 0.58/0.79  thf('47', plain,
% 0.58/0.79      ((![X0 : $i]: (zip_tseitin_4 @ sk_A @ X0))
% 0.58/0.79         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.79  thf('48', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.58/0.79      inference('sat_resolution*', [status(thm)], ['23', '26', '27'])).
% 0.58/0.79  thf('49', plain, (![X0 : $i]: (zip_tseitin_4 @ sk_A @ X0)),
% 0.58/0.79      inference('simpl_trail', [status(thm)], ['47', '48'])).
% 0.58/0.79  thf('50', plain, ((zip_tseitin_5 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.58/0.79      inference('demod', [status(thm)], ['33', '49'])).
% 0.58/0.79  thf('51', plain, ($false), inference('demod', [status(thm)], ['30', '50'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

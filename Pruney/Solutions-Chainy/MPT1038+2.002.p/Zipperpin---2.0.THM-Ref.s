%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B5jJ3rTmgb

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:15 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 376 expanded)
%              Number of leaves         :   17 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  497 (7958 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t152_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ A @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
             => ( ( ( r1_partfun1 @ B @ D )
                  & ( r1_partfun1 @ C @ D ) )
               => ( r1_partfun1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ A @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
               => ( ( ( r1_partfun1 @ B @ D )
                    & ( r1_partfun1 @ C @ D ) )
                 => ( r1_partfun1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_funct_2])).

thf('0',plain,(
    ~ ( r1_partfun1 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t158_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ( ( ( r1_partfun1 @ C @ E )
                  & ( r1_partfun1 @ D @ E )
                  & ( v1_partfun1 @ E @ A ) )
               => ( r1_partfun1 @ C @ D ) ) ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r1_partfun1 @ X28 @ X25 )
      | ~ ( r1_partfun1 @ X28 @ X29 )
      | ~ ( r1_partfun1 @ X25 @ X29 )
      | ~ ( v1_partfun1 @ X29 @ X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t158_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X1 @ sk_A )
      | ~ ( r1_partfun1 @ sk_C @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ( r1_partfun1 @ X0 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_partfun1 @ X1 @ sk_A )
      | ~ ( r1_partfun1 @ sk_C @ X1 )
      | ~ ( r1_partfun1 @ X0 @ X1 )
      | ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_B_1 @ sk_C )
      | ~ ( r1_partfun1 @ sk_B_1 @ X0 )
      | ~ ( r1_partfun1 @ sk_C @ X0 )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_partfun1 @ sk_B_1 @ sk_C )
      | ~ ( r1_partfun1 @ sk_B_1 @ X0 )
      | ~ ( r1_partfun1 @ sk_C @ X0 )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ~ ( r1_partfun1 @ sk_B_1 @ sk_D )
    | ( r1_partfun1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_partfun1 @ sk_B_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_partfun1 @ sk_D @ sk_A )
    | ( r1_partfun1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ~ ( r1_partfun1 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','26'])).

thf('28',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['3','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','26'])).

thf('33',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B_1 = sk_C ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ~ ( r1_partfun1 @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['0','36'])).

thf('38',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B_1 = sk_C ),
    inference('sup-',[status(thm)],['28','35'])).

thf('40',plain,(
    r1_partfun1 @ sk_B_1 @ sk_D ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['9','26'])).

thf('45',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('47',plain,(
    sk_B_1 = sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_partfun1 @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['37','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B5jJ3rTmgb
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 456 iterations in 0.251s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.70  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.52/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.70  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.52/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.70  thf(t152_funct_2, conjecture,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( v1_funct_1 @ B ) & 
% 0.52/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.70             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.52/0.70           ( ![D:$i]:
% 0.52/0.70             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ A ) & 
% 0.52/0.70                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.52/0.70               ( ( ( r1_partfun1 @ B @ D ) & ( r1_partfun1 @ C @ D ) ) =>
% 0.52/0.70                 ( r1_partfun1 @ B @ C ) ) ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i,B:$i]:
% 0.52/0.70        ( ( ( v1_funct_1 @ B ) & 
% 0.52/0.70            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.52/0.70          ( ![C:$i]:
% 0.52/0.70            ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.70                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.52/0.70              ( ![D:$i]:
% 0.52/0.70                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ A ) & 
% 0.52/0.70                    ( m1_subset_1 @
% 0.52/0.70                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.52/0.70                  ( ( ( r1_partfun1 @ B @ D ) & ( r1_partfun1 @ C @ D ) ) =>
% 0.52/0.70                    ( r1_partfun1 @ B @ C ) ) ) ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t152_funct_2])).
% 0.52/0.70  thf('0', plain, (~ (r1_partfun1 @ sk_B_1 @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(cc4_relset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_xboole_0 @ A ) =>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.52/0.70           ( v1_xboole_0 @ C ) ) ) ))).
% 0.52/0.70  thf('2', plain,
% 0.52/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X19)
% 0.52/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.52/0.70          | (v1_xboole_0 @ X20))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.52/0.70  thf('3', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(cc5_funct_2, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.70       ( ![C:$i]:
% 0.52/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.70           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.52/0.70             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.52/0.70          | (v1_partfun1 @ X22 @ X23)
% 0.52/0.70          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.52/0.70          | ~ (v1_funct_1 @ X22)
% 0.52/0.70          | (v1_xboole_0 @ X24))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.52/0.70  thf('6', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_A)
% 0.52/0.70        | ~ (v1_funct_1 @ sk_D)
% 0.52/0.70        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_A)
% 0.52/0.70        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.70  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('9', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.52/0.70  thf('10', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('11', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('12', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(t158_partfun1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.70       ( ![D:$i]:
% 0.52/0.70         ( ( ( v1_funct_1 @ D ) & 
% 0.52/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.70           ( ![E:$i]:
% 0.52/0.70             ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.70                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.70               ( ( ( r1_partfun1 @ C @ E ) & ( r1_partfun1 @ D @ E ) & 
% 0.52/0.70                   ( v1_partfun1 @ E @ A ) ) =>
% 0.52/0.70                 ( r1_partfun1 @ C @ D ) ) ) ) ) ) ))).
% 0.52/0.70  thf('13', plain,
% 0.52/0.70      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.70         (~ (v1_funct_1 @ X25)
% 0.52/0.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.52/0.70          | (r1_partfun1 @ X28 @ X25)
% 0.52/0.70          | ~ (r1_partfun1 @ X28 @ X29)
% 0.52/0.70          | ~ (r1_partfun1 @ X25 @ X29)
% 0.52/0.70          | ~ (v1_partfun1 @ X29 @ X26)
% 0.52/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.52/0.70          | ~ (v1_funct_1 @ X29)
% 0.52/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.52/0.70          | ~ (v1_funct_1 @ X28))),
% 0.52/0.70      inference('cnf', [status(esa)], [t158_partfun1])).
% 0.52/0.70  thf('14', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_funct_1 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.52/0.70          | ~ (v1_funct_1 @ X1)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.52/0.70          | ~ (v1_partfun1 @ X1 @ sk_A)
% 0.52/0.70          | ~ (r1_partfun1 @ sk_C @ X1)
% 0.52/0.70          | ~ (r1_partfun1 @ X0 @ X1)
% 0.52/0.70          | (r1_partfun1 @ X0 @ sk_C)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.70  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('16', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (~ (v1_funct_1 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.52/0.70          | ~ (v1_funct_1 @ X1)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.52/0.70          | ~ (v1_partfun1 @ X1 @ sk_A)
% 0.52/0.70          | ~ (r1_partfun1 @ sk_C @ X1)
% 0.52/0.70          | ~ (r1_partfun1 @ X0 @ X1)
% 0.52/0.70          | (r1_partfun1 @ X0 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['14', '15'])).
% 0.52/0.70  thf('17', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r1_partfun1 @ sk_B_1 @ sk_C)
% 0.52/0.70          | ~ (r1_partfun1 @ sk_B_1 @ X0)
% 0.52/0.70          | ~ (r1_partfun1 @ sk_C @ X0)
% 0.52/0.70          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.52/0.70          | ~ (v1_funct_1 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_B_1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['11', '16'])).
% 0.52/0.70  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((r1_partfun1 @ sk_B_1 @ sk_C)
% 0.52/0.70          | ~ (r1_partfun1 @ sk_B_1 @ X0)
% 0.52/0.70          | ~ (r1_partfun1 @ sk_C @ X0)
% 0.52/0.70          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.52/0.70          | ~ (v1_funct_1 @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['17', '18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      ((~ (v1_funct_1 @ sk_D)
% 0.52/0.70        | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.52/0.70        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.52/0.70        | ~ (r1_partfun1 @ sk_B_1 @ sk_D)
% 0.52/0.70        | (r1_partfun1 @ sk_B_1 @ sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '19'])).
% 0.52/0.70  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('22', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('23', plain, ((r1_partfun1 @ sk_B_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      ((~ (v1_partfun1 @ sk_D @ sk_A) | (r1_partfun1 @ sk_B_1 @ sk_C))),
% 0.52/0.70      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.52/0.70  thf('25', plain, (~ (r1_partfun1 @ sk_B_1 @ sk_C)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('26', plain, (~ (v1_partfun1 @ sk_D @ sk_A)),
% 0.52/0.70      inference('clc', [status(thm)], ['24', '25'])).
% 0.52/0.70  thf('27', plain, ((v1_xboole_0 @ sk_A)),
% 0.52/0.70      inference('sup-', [status(thm)], ['9', '26'])).
% 0.52/0.70  thf('28', plain, ((v1_xboole_0 @ sk_C)),
% 0.52/0.70      inference('demod', [status(thm)], ['3', '27'])).
% 0.52/0.70  thf('29', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('30', plain,
% 0.52/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X19)
% 0.52/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.52/0.70          | (v1_xboole_0 @ X20))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.52/0.70  thf('31', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.70  thf('32', plain, ((v1_xboole_0 @ sk_A)),
% 0.52/0.70      inference('sup-', [status(thm)], ['9', '26'])).
% 0.52/0.70  thf('33', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.52/0.70      inference('demod', [status(thm)], ['31', '32'])).
% 0.52/0.70  thf(t8_boole, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.52/0.70  thf('34', plain,
% 0.52/0.70      (![X3 : $i, X4 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t8_boole])).
% 0.52/0.70  thf('35', plain, (![X0 : $i]: (((sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.70  thf('36', plain, (((sk_B_1) = (sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['28', '35'])).
% 0.52/0.70  thf('37', plain, (~ (r1_partfun1 @ sk_B_1 @ sk_B_1)),
% 0.52/0.70      inference('demod', [status(thm)], ['0', '36'])).
% 0.52/0.70  thf('38', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('39', plain, (((sk_B_1) = (sk_C))),
% 0.52/0.70      inference('sup-', [status(thm)], ['28', '35'])).
% 0.52/0.70  thf('40', plain, ((r1_partfun1 @ sk_B_1 @ sk_D)),
% 0.52/0.70      inference('demod', [status(thm)], ['38', '39'])).
% 0.52/0.70  thf('41', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('42', plain,
% 0.52/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.70         (~ (v1_xboole_0 @ X19)
% 0.52/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.52/0.70          | (v1_xboole_0 @ X20))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.52/0.70  thf('43', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.52/0.70  thf('44', plain, ((v1_xboole_0 @ sk_A)),
% 0.52/0.70      inference('sup-', [status(thm)], ['9', '26'])).
% 0.52/0.70  thf('45', plain, ((v1_xboole_0 @ sk_D)),
% 0.52/0.70      inference('demod', [status(thm)], ['43', '44'])).
% 0.52/0.70  thf('46', plain, (![X0 : $i]: (((sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.52/0.70  thf('47', plain, (((sk_B_1) = (sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.70  thf('48', plain, ((r1_partfun1 @ sk_B_1 @ sk_B_1)),
% 0.52/0.70      inference('demod', [status(thm)], ['40', '47'])).
% 0.52/0.70  thf('49', plain, ($false), inference('demod', [status(thm)], ['37', '48'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

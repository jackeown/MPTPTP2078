%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eFuTYhrljw

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 122 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :  519 (1860 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X5 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ X6 )
      | ( m1_subset_1 @ ( k3_funct_2 @ X6 @ X7 @ X5 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['0','8'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r2_hidden @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['11','12'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('15',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( v1_funct_2 @ X9 @ X10 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ X10 )
      | ( ( k3_funct_2 @ X10 @ X11 @ X9 @ X12 )
        = ( k1_funct_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k1_funct_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_B @ ( k1_funct_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X13 ) @ ( k2_relset_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C )
    = ( k1_funct_1 @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('41',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['26','42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eFuTYhrljw
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:21:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 31 iterations in 0.020s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t189_funct_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.47               ( ![D:$i]:
% 0.21/0.47                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.47                     ( m1_subset_1 @
% 0.21/0.47                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.47                   ( r2_hidden @
% 0.21/0.47                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.21/0.47                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.47                  ( ![D:$i]:
% 0.21/0.47                    ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.47                        ( m1_subset_1 @
% 0.21/0.47                          D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.47                      ( r2_hidden @
% 0.21/0.47                        ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.21/0.47                        ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t189_funct_2])).
% 0.21/0.47  thf('0', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_k3_funct_2, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.47         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.47         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.47       ( m1_subset_1 @ ( k3_funct_2 @ A @ B @ C @ D ) @ B ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7)))
% 0.21/0.47          | ~ (v1_funct_2 @ X5 @ X6 @ X7)
% 0.21/0.47          | ~ (v1_funct_1 @ X5)
% 0.21/0.47          | (v1_xboole_0 @ X6)
% 0.21/0.47          | ~ (m1_subset_1 @ X8 @ X6)
% 0.21/0.47          | (m1_subset_1 @ (k3_funct_2 @ X6 @ X7 @ X5 @ X8) @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k3_funct_2])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) @ sk_B)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.47          | (v1_xboole_0 @ sk_A)
% 0.21/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) @ sk_B)
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.47          | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.47  thf('7', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.47          | (m1_subset_1 @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) @ sk_B))),
% 0.21/0.47      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((m1_subset_1 @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_B)),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '8'])).
% 0.21/0.47  thf(t2_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ X1 @ X2)
% 0.21/0.47          | (v1_xboole_0 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_B)
% 0.21/0.47        | (r2_hidden @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      ((r2_hidden @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_B)),
% 0.21/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.21/0.47  thf(t7_ordinal1, axiom,
% 0.21/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]: (~ (r2_hidden @ X3 @ X4) | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (~ (r1_tarski @ sk_B @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.47         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.47         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.47       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.21/0.47          | ~ (v1_funct_2 @ X9 @ X10 @ X11)
% 0.21/0.47          | ~ (v1_funct_1 @ X9)
% 0.21/0.47          | (v1_xboole_0 @ X10)
% 0.21/0.47          | ~ (m1_subset_1 @ X12 @ X10)
% 0.21/0.47          | ((k3_funct_2 @ X10 @ X11 @ X9 @ X12) = (k1_funct_1 @ X9 @ X12)))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.47          | (v1_xboole_0 @ sk_A)
% 0.21/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.47  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.21/0.47          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.47          | (v1_xboole_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.47  thf('23', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.47          | ((k3_funct_2 @ sk_A @ sk_B @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.21/0.47      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) = (k1_funct_1 @ sk_D @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '24'])).
% 0.21/0.47  thf('26', plain, (~ (r1_tarski @ sk_B @ (k1_funct_1 @ sk_D @ sk_C))),
% 0.21/0.47      inference('demod', [status(thm)], ['15', '25'])).
% 0.21/0.47  thf('27', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X1 : $i, X2 : $i]:
% 0.21/0.47         ((r2_hidden @ X1 @ X2)
% 0.21/0.47          | (v1_xboole_0 @ X2)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.47  thf('29', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('31', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.21/0.47      inference('clc', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t6_funct_2, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.47       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.47         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.47           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X13 @ X14)
% 0.21/0.47          | ((X15) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_funct_1 @ X16)
% 0.21/0.47          | ~ (v1_funct_2 @ X16 @ X14 @ X15)
% 0.21/0.47          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.21/0.47          | (r2_hidden @ (k1_funct_1 @ X16 @ X13) @ 
% 0.21/0.47             (k2_relset_1 @ X14 @ X15 @ X16)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.21/0.47  thf('34', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.47           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.47          | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.21/0.47          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.47          | ((sk_B) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.47  thf('35', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('36', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.21/0.47           (k2_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.21/0.47          | ((sk_B) = (k1_xboole_0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.47  thf('38', plain,
% 0.21/0.47      ((((sk_B) = (k1_xboole_0))
% 0.21/0.47        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ 
% 0.21/0.47           (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '37'])).
% 0.21/0.47  thf('39', plain,
% 0.21/0.47      (~ (r2_hidden @ (k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.47          (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (((k3_funct_2 @ sk_A @ sk_B @ sk_D @ sk_C) = (k1_funct_1 @ sk_D @ sk_C))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '24'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (~ (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C) @ 
% 0.21/0.47          (k2_relset_1 @ sk_A @ sk_B @ sk_D))),
% 0.21/0.47      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.47  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('43', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('44', plain, ($false),
% 0.21/0.47      inference('demod', [status(thm)], ['26', '42', '43'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

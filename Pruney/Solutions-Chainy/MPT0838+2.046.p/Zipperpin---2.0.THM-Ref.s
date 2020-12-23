%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p51wOzOjBh

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:05 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 110 expanded)
%              Number of leaves         :   34 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  471 ( 939 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('0',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X28 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_2 ),
    inference(demod,[status(thm)],['18','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['12','29'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X16: $i] :
      ( ( ( k2_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('37',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36'])).

thf(s3_funct_1__e9_44_1__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('38',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('39',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('45',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['4','37','45'])).

thf('47',plain,(
    $false ),
    inference(simplify,[status(thm)],['46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.p51wOzOjBh
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 117 iterations in 0.094s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.56  thf(t49_relset_1, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.56           ( ![C:$i]:
% 0.39/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.39/0.56                    ( ![D:$i]:
% 0.39/0.56                      ( ( m1_subset_1 @ D @ B ) =>
% 0.39/0.56                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.56              ( ![C:$i]:
% 0.39/0.56                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.39/0.56                       ( ![D:$i]:
% 0.39/0.56                         ( ( m1_subset_1 @ D @ B ) =>
% 0.39/0.56                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.39/0.56  thf('0', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) != (k1_xboole_0))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.56         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.39/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.56  thf('4', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.56  thf(d1_xboole_0, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (![X28 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X28 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 0.39/0.56          | ~ (m1_subset_1 @ X28 @ sk_B_2))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (((v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 0.39/0.56        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1)) @ 
% 0.39/0.56             sk_B_2))),
% 0.39/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.56         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 0.39/0.56          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.39/0.56        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_2))),
% 0.39/0.56      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.39/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc2_relset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.56         ((v5_relat_1 @ X19 @ X21)
% 0.39/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.56  thf('16', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_2)),
% 0.39/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.56  thf(d19_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ B ) =>
% 0.39/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (![X12 : $i, X13 : $i]:
% 0.39/0.56         (~ (v5_relat_1 @ X12 @ X13)
% 0.39/0.56          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.39/0.56          | ~ (v1_relat_1 @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2))),
% 0.39/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(cc2_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      (![X10 : $i, X11 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.39/0.56          | (v1_relat_1 @ X10)
% 0.39/0.56          | ~ (v1_relat_1 @ X11))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_C_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.56  thf(fc6_relat_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.56  thf('22', plain,
% 0.39/0.56      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.56  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.56  thf('24', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_2)),
% 0.39/0.56      inference('demod', [status(thm)], ['18', '23'])).
% 0.39/0.56  thf(d3_tarski, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X3 @ X4)
% 0.39/0.56          | (r2_hidden @ X3 @ X5)
% 0.39/0.56          | ~ (r1_tarski @ X4 @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((r2_hidden @ X0 @ sk_B_2)
% 0.39/0.56          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.39/0.56        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_2))),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '26'])).
% 0.39/0.56  thf(t1_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.39/0.56  thf('28', plain,
% 0.39/0.56      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.39/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 0.39/0.56        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_2))),
% 0.39/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.56  thf('30', plain, ((v1_xboole_0 @ (k2_relat_1 @ sk_C_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['12', '29'])).
% 0.39/0.56  thf(l13_xboole_0, axiom,
% 0.39/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.39/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.39/0.56  thf(t64_relat_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_relat_1 @ A ) =>
% 0.39/0.56       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.56           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.56         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      (![X16 : $i]:
% 0.39/0.56         (((k2_relat_1 @ X16) != (k1_xboole_0))
% 0.39/0.56          | ((X16) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_relat_1 @ X16))),
% 0.39/0.56      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (((k2_relat_1 @ X1) != (X0))
% 0.39/0.56          | ~ (v1_xboole_0 @ X0)
% 0.39/0.56          | ~ (v1_relat_1 @ X1)
% 0.39/0.56          | ((X1) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (![X1 : $i]:
% 0.39/0.56         (((X1) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_relat_1 @ X1)
% 0.39/0.56          | ~ (v1_xboole_0 @ (k2_relat_1 @ X1)))),
% 0.39/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.39/0.56  thf('35', plain, ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['30', '34'])).
% 0.39/0.56  thf('36', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.56  thf('37', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.56  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ?[B:$i]:
% 0.39/0.56       ( ( ![C:$i]:
% 0.39/0.56           ( ( r2_hidden @ C @ A ) =>
% 0.39/0.56             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.56         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.39/0.56         ( v1_relat_1 @ B ) ) ))).
% 0.39/0.56  thf('38', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B_1 @ X17)) = (X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      (![X16 : $i]:
% 0.39/0.56         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.39/0.56          | ((X16) = (k1_xboole_0))
% 0.39/0.56          | ~ (v1_relat_1 @ X16))),
% 0.39/0.56      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.39/0.56  thf('40', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (((X0) != (k1_xboole_0))
% 0.39/0.56          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.39/0.56          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('41', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B_1 @ X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.39/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.56  thf('43', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.39/0.56  thf('44', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B_1 @ X17)) = (X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.39/0.56  thf('45', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('46', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.39/0.56      inference('demod', [status(thm)], ['4', '37', '45'])).
% 0.39/0.56  thf('47', plain, ($false), inference('simplify', [status(thm)], ['46'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

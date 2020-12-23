%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oWsnx89drS

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:16 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 198 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  547 (1780 expanded)
%              Number of equality atoms :   28 (  68 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('0',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X43 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X43 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_C_3 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['15','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X43: $i] :
      ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','26'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X30: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X30 ) @ ( sk_C_2 @ X30 ) ) @ X30 )
      | ( X30 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X21 @ X24 )
      | ( X24
       != ( k1_relat_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X21 @ ( k1_relat_1 @ X23 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_3 ) @ k1_xboole_0 )
    | ( sk_C_3 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['31','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['18','19'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_3 ) @ k1_xboole_0 )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X43: $i] :
      ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['10','25'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','30'])).

thf('41',plain,(
    ! [X43: $i] :
      ~ ( r2_hidden @ X43 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference(clc,[status(thm)],['38','41'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('43',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X34 @ X35 @ X36 ) @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('47',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('53',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['4','42','53'])).

thf('55',plain,(
    $false ),
    inference(simplify,[status(thm)],['54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oWsnx89drS
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.60  % Solved by: fo/fo7.sh
% 0.36/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.60  % done 266 iterations in 0.128s
% 0.36/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.60  % SZS output start Refutation
% 0.36/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.60  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.36/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.60  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.36/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.60  thf(t50_relset_1, conjecture,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.60           ( ![C:$i]:
% 0.36/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.60               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.60                    ( ![D:$i]:
% 0.36/0.60                      ( ( m1_subset_1 @ D @ B ) =>
% 0.36/0.60                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.60    (~( ![A:$i]:
% 0.36/0.60        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.60          ( ![B:$i]:
% 0.36/0.60            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.60              ( ![C:$i]:
% 0.36/0.60                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.60                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.36/0.60                       ( ![D:$i]:
% 0.36/0.60                         ( ( m1_subset_1 @ D @ B ) =>
% 0.36/0.60                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.60    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.36/0.60  thf('0', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) != (k1_xboole_0))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('1', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.60  thf('2', plain,
% 0.36/0.60      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.60         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.36/0.60          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.60  thf('3', plain,
% 0.36/0.60      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.36/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.60  thf('4', plain, (((k2_relat_1 @ sk_C_3) != (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.60  thf(d3_tarski, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.60  thf('5', plain,
% 0.36/0.60      (![X1 : $i, X3 : $i]:
% 0.36/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.60  thf('6', plain,
% 0.36/0.60      (![X43 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X43 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3))
% 0.36/0.60          | ~ (m1_subset_1 @ X43 @ sk_B_1))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf('7', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.60  thf('8', plain,
% 0.36/0.60      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.36/0.60         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.36/0.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.60  thf('9', plain,
% 0.36/0.60      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.36/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.60  thf('10', plain,
% 0.36/0.60      (![X43 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X43 @ (k1_relat_1 @ sk_C_3))
% 0.36/0.60          | ~ (m1_subset_1 @ X43 @ sk_B_1))),
% 0.36/0.60      inference('demod', [status(thm)], ['6', '9'])).
% 0.36/0.60  thf('11', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(cc2_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.60  thf('12', plain,
% 0.36/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.60         ((v4_relat_1 @ X31 @ X32)
% 0.36/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.36/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.60  thf('13', plain, ((v4_relat_1 @ sk_C_3 @ sk_B_1)),
% 0.36/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.60  thf(d18_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ B ) =>
% 0.36/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.60  thf('14', plain,
% 0.36/0.60      (![X19 : $i, X20 : $i]:
% 0.36/0.60         (~ (v4_relat_1 @ X19 @ X20)
% 0.36/0.60          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.36/0.60          | ~ (v1_relat_1 @ X19))),
% 0.36/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.36/0.60  thf('15', plain,
% 0.36/0.60      ((~ (v1_relat_1 @ sk_C_3) | (r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.60  thf('16', plain,
% 0.36/0.60      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.36/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.60  thf(cc2_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) =>
% 0.36/0.60       ( ![B:$i]:
% 0.36/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.60  thf('17', plain,
% 0.36/0.60      (![X17 : $i, X18 : $i]:
% 0.36/0.60         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.36/0.60          | (v1_relat_1 @ X17)
% 0.36/0.60          | ~ (v1_relat_1 @ X18))),
% 0.36/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.60  thf('18', plain,
% 0.36/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_C_3))),
% 0.36/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.60  thf(fc6_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.60  thf('19', plain,
% 0.36/0.60      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.36/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.60  thf('20', plain, ((v1_relat_1 @ sk_C_3)),
% 0.36/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.60  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1)),
% 0.36/0.60      inference('demod', [status(thm)], ['15', '20'])).
% 0.36/0.60  thf(t3_subset, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.60  thf('22', plain,
% 0.36/0.60      (![X11 : $i, X13 : $i]:
% 0.36/0.60         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.60  thf('23', plain,
% 0.36/0.60      ((m1_subset_1 @ (k1_relat_1 @ sk_C_3) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.36/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.60  thf(t4_subset, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.36/0.60       ( m1_subset_1 @ A @ C ) ))).
% 0.36/0.60  thf('24', plain,
% 0.36/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.60         (~ (r2_hidden @ X14 @ X15)
% 0.36/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.36/0.60          | (m1_subset_1 @ X14 @ X16))),
% 0.36/0.60      inference('cnf', [status(esa)], [t4_subset])).
% 0.36/0.60  thf('25', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.36/0.60          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.60  thf('26', plain, (![X43 : $i]: ~ (r2_hidden @ X43 @ (k1_relat_1 @ sk_C_3))),
% 0.36/0.60      inference('clc', [status(thm)], ['10', '25'])).
% 0.36/0.60  thf('27', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_C_3) @ X0)),
% 0.36/0.60      inference('sup-', [status(thm)], ['5', '26'])).
% 0.36/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.60  thf('28', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.60  thf(d10_xboole_0, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.60  thf('29', plain,
% 0.36/0.60      (![X4 : $i, X6 : $i]:
% 0.36/0.60         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.36/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.60  thf('30', plain,
% 0.36/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('31', plain, (((k1_relat_1 @ sk_C_3) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.36/0.60  thf(t56_relat_1, axiom,
% 0.36/0.60    (![A:$i]:
% 0.36/0.60     ( ( v1_relat_1 @ A ) =>
% 0.36/0.60       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.36/0.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.60  thf('32', plain,
% 0.36/0.60      (![X30 : $i]:
% 0.36/0.60         ((r2_hidden @ (k4_tarski @ (sk_B @ X30) @ (sk_C_2 @ X30)) @ X30)
% 0.36/0.60          | ((X30) = (k1_xboole_0))
% 0.36/0.60          | ~ (v1_relat_1 @ X30))),
% 0.36/0.60      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.36/0.60  thf(d4_relat_1, axiom,
% 0.36/0.60    (![A:$i,B:$i]:
% 0.36/0.60     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.36/0.60       ( ![C:$i]:
% 0.36/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.36/0.60  thf('33', plain,
% 0.36/0.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.36/0.60         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 0.36/0.60          | (r2_hidden @ X21 @ X24)
% 0.36/0.60          | ((X24) != (k1_relat_1 @ X23)))),
% 0.36/0.60      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.36/0.60  thf('34', plain,
% 0.36/0.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.60         ((r2_hidden @ X21 @ (k1_relat_1 @ X23))
% 0.36/0.60          | ~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23))),
% 0.36/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.60  thf('35', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (~ (v1_relat_1 @ X0)
% 0.36/0.60          | ((X0) = (k1_xboole_0))
% 0.36/0.60          | (r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['32', '34'])).
% 0.36/0.60  thf('36', plain,
% 0.36/0.60      (((r2_hidden @ (sk_B @ sk_C_3) @ k1_xboole_0)
% 0.36/0.60        | ((sk_C_3) = (k1_xboole_0))
% 0.36/0.60        | ~ (v1_relat_1 @ sk_C_3))),
% 0.36/0.60      inference('sup+', [status(thm)], ['31', '35'])).
% 0.36/0.60  thf('37', plain, ((v1_relat_1 @ sk_C_3)),
% 0.36/0.60      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.60  thf('38', plain,
% 0.36/0.60      (((r2_hidden @ (sk_B @ sk_C_3) @ k1_xboole_0)
% 0.36/0.60        | ((sk_C_3) = (k1_xboole_0)))),
% 0.36/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.36/0.60  thf('39', plain, (![X43 : $i]: ~ (r2_hidden @ X43 @ (k1_relat_1 @ sk_C_3))),
% 0.36/0.60      inference('clc', [status(thm)], ['10', '25'])).
% 0.36/0.60  thf('40', plain, (((k1_relat_1 @ sk_C_3) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['27', '30'])).
% 0.36/0.60  thf('41', plain, (![X43 : $i]: ~ (r2_hidden @ X43 @ k1_xboole_0)),
% 0.36/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.60  thf('42', plain, (((sk_C_3) = (k1_xboole_0))),
% 0.36/0.60      inference('clc', [status(thm)], ['38', '41'])).
% 0.36/0.60  thf(t4_subset_1, axiom,
% 0.36/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.60  thf('43', plain,
% 0.36/0.60      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.36/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.60  thf(dt_k2_relset_1, axiom,
% 0.36/0.60    (![A:$i,B:$i,C:$i]:
% 0.36/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.60       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.36/0.60  thf('44', plain,
% 0.36/0.60      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.60         ((m1_subset_1 @ (k2_relset_1 @ X34 @ X35 @ X36) @ (k1_zfmisc_1 @ X35))
% 0.36/0.60          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.36/0.60      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.36/0.60  thf('45', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         (m1_subset_1 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 0.36/0.60          (k1_zfmisc_1 @ X0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.60  thf('46', plain,
% 0.36/0.60      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.36/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.60  thf('47', plain,
% 0.36/0.60      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.60         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.36/0.60          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.36/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.60  thf('48', plain,
% 0.36/0.60      (![X0 : $i, X1 : $i]:
% 0.36/0.60         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.60  thf('49', plain,
% 0.36/0.60      (![X0 : $i]:
% 0.36/0.60         (m1_subset_1 @ (k2_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.36/0.60      inference('demod', [status(thm)], ['45', '48'])).
% 0.36/0.60  thf('50', plain,
% 0.36/0.60      (![X11 : $i, X12 : $i]:
% 0.36/0.60         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.36/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.60  thf('51', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.36/0.60      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.60  thf('52', plain,
% 0.36/0.60      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.60  thf('53', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.60  thf('54', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.60      inference('demod', [status(thm)], ['4', '42', '53'])).
% 0.36/0.60  thf('55', plain, ($false), inference('simplify', [status(thm)], ['54'])).
% 0.36/0.60  
% 0.36/0.60  % SZS output end Refutation
% 0.36/0.60  
% 0.36/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

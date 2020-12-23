%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AlUaTjzepn

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:04 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 131 expanded)
%              Number of leaves         :   38 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  520 (1042 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21
        = ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X21 @ X18 ) @ ( sk_D @ X21 @ X18 ) ) @ X18 )
      | ( r2_hidden @ ( sk_C_2 @ X21 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_5 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k1_relset_1 @ X39 @ X40 @ X38 )
        = ( k1_relat_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_5 )
    = ( k1_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ( k1_relat_1 @ sk_C_5 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_C_5 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ~ ( v1_xboole_0 @ sk_C_5 ) ),
    inference('simplify_reflect+',[status(thm)],['11','16'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('18',plain,(
    ! [X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B_1 @ X32 ) @ ( sk_C_4 @ X32 ) ) @ X32 )
      | ( X32 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ X25 )
      | ( r2_hidden @ X24 @ X26 )
      | ( X26
       != ( k2_relat_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ ( k2_relat_1 @ X25 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ X24 ) @ X25 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_4 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_5 ) )
      | ~ ( m1_subset_1 @ X44 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k2_relset_1 @ X42 @ X43 @ X41 )
        = ( k2_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_5 )
    = ( k2_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ X44 @ ( k2_relat_1 @ sk_C_5 ) )
      | ~ ( m1_subset_1 @ X44 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( sk_C_5 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_5 )
    | ~ ( m1_subset_1 @ ( sk_C_4 @ sk_C_5 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_C_5 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_C_4 @ sk_C_5 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_4 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( v5_relat_1 @ X35 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_C_5 @ sk_B_2 ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C_5 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_5 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_5 ) @ sk_B_2 ),
    inference(demod,[status(thm)],['39','40'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_5 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C_5 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_5 )
    | ( r2_hidden @ ( sk_C_4 @ sk_C_5 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference(demod,[status(thm)],['30','31'])).

thf('46',plain,
    ( ( sk_C_5 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_4 @ sk_C_5 ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('48',plain,
    ( ( sk_C_5 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C_4 @ sk_C_5 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_C_5 = k1_xboole_0 ),
    inference(clc,[status(thm)],['33','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','15'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['17','49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AlUaTjzepn
% 0.14/0.37  % Computer   : n004.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 12:34:09 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.47/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.70  % Solved by: fo/fo7.sh
% 0.47/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.70  % done 228 iterations in 0.211s
% 0.47/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.70  % SZS output start Refutation
% 0.47/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.47/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.47/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.70  thf(sk_C_5_type, type, sk_C_5: $i).
% 0.47/0.70  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.47/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.70  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.47/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.70  thf(sk_C_4_type, type, sk_C_4: $i > $i).
% 0.47/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.70  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.47/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.70  thf(d4_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.47/0.70       ( ![C:$i]:
% 0.47/0.70         ( ( r2_hidden @ C @ B ) <=>
% 0.47/0.70           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.47/0.70  thf('0', plain,
% 0.47/0.70      (![X18 : $i, X21 : $i]:
% 0.47/0.70         (((X21) = (k1_relat_1 @ X18))
% 0.47/0.70          | (r2_hidden @ 
% 0.47/0.70             (k4_tarski @ (sk_C_2 @ X21 @ X18) @ (sk_D @ X21 @ X18)) @ X18)
% 0.47/0.70          | (r2_hidden @ (sk_C_2 @ X21 @ X18) @ X21))),
% 0.47/0.70      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.47/0.70  thf(d1_xboole_0, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.70  thf('1', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.70  thf('2', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         ((r2_hidden @ (sk_C_2 @ X1 @ X0) @ X1)
% 0.47/0.70          | ((X1) = (k1_relat_1 @ X0))
% 0.47/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.70  thf('3', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.47/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.70  thf('4', plain,
% 0.47/0.70      (![X0 : $i, X1 : $i]:
% 0.47/0.70         (~ (v1_xboole_0 @ X1)
% 0.47/0.70          | ((X0) = (k1_relat_1 @ X1))
% 0.47/0.70          | ~ (v1_xboole_0 @ X0))),
% 0.47/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.70  thf(t49_relset_1, conjecture,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.70           ( ![C:$i]:
% 0.47/0.70             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.47/0.70                    ( ![D:$i]:
% 0.47/0.70                      ( ( m1_subset_1 @ D @ B ) =>
% 0.47/0.70                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.70    (~( ![A:$i]:
% 0.47/0.70        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.70          ( ![B:$i]:
% 0.47/0.70            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.70              ( ![C:$i]:
% 0.47/0.70                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.47/0.70                       ( ![D:$i]:
% 0.47/0.70                         ( ( m1_subset_1 @ D @ B ) =>
% 0.47/0.70                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.70    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.47/0.70  thf('5', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_5) != (k1_xboole_0))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('6', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.70  thf('7', plain,
% 0.47/0.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.47/0.70         (((k1_relset_1 @ X39 @ X40 @ X38) = (k1_relat_1 @ X38))
% 0.47/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40))))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.70  thf('8', plain,
% 0.47/0.70      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_5) = (k1_relat_1 @ sk_C_5))),
% 0.47/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.47/0.70  thf('9', plain, (((k1_relat_1 @ sk_C_5) != (k1_xboole_0))),
% 0.47/0.70      inference('demod', [status(thm)], ['5', '8'])).
% 0.47/0.70  thf('10', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (((X0) != (k1_xboole_0))
% 0.47/0.70          | ~ (v1_xboole_0 @ X0)
% 0.47/0.70          | ~ (v1_xboole_0 @ sk_C_5))),
% 0.47/0.70      inference('sup-', [status(thm)], ['4', '9'])).
% 0.47/0.70  thf('11', plain,
% 0.47/0.70      ((~ (v1_xboole_0 @ sk_C_5) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.47/0.70      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.70  thf('12', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.47/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.70  thf('13', plain,
% 0.47/0.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.70  thf(t7_ordinal1, axiom,
% 0.47/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.70  thf('14', plain,
% 0.47/0.70      (![X33 : $i, X34 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X33 @ X34) | ~ (r1_tarski @ X34 @ X33))),
% 0.47/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.47/0.70  thf('15', plain,
% 0.47/0.70      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.47/0.70  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['12', '15'])).
% 0.47/0.70  thf('17', plain, (~ (v1_xboole_0 @ sk_C_5)),
% 0.47/0.70      inference('simplify_reflect+', [status(thm)], ['11', '16'])).
% 0.47/0.70  thf(t56_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.47/0.70         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.47/0.70  thf('18', plain,
% 0.47/0.70      (![X32 : $i]:
% 0.47/0.70         ((r2_hidden @ (k4_tarski @ (sk_B_1 @ X32) @ (sk_C_4 @ X32)) @ X32)
% 0.47/0.70          | ((X32) = (k1_xboole_0))
% 0.47/0.70          | ~ (v1_relat_1 @ X32))),
% 0.47/0.70      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.47/0.70  thf(d5_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.47/0.70       ( ![C:$i]:
% 0.47/0.70         ( ( r2_hidden @ C @ B ) <=>
% 0.47/0.70           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.47/0.70  thf('19', plain,
% 0.47/0.70      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.70         (~ (r2_hidden @ (k4_tarski @ X23 @ X24) @ X25)
% 0.47/0.70          | (r2_hidden @ X24 @ X26)
% 0.47/0.70          | ((X26) != (k2_relat_1 @ X25)))),
% 0.47/0.70      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.47/0.70  thf('20', plain,
% 0.47/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.47/0.70         ((r2_hidden @ X24 @ (k2_relat_1 @ X25))
% 0.47/0.70          | ~ (r2_hidden @ (k4_tarski @ X23 @ X24) @ X25))),
% 0.47/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.47/0.70  thf('21', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | ((X0) = (k1_xboole_0))
% 0.47/0.70          | (r2_hidden @ (sk_C_4 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['18', '20'])).
% 0.47/0.70  thf('22', plain,
% 0.47/0.70      (![X44 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X44 @ (k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_5))
% 0.47/0.70          | ~ (m1_subset_1 @ X44 @ sk_B_2))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf('23', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.70  thf('24', plain,
% 0.47/0.70      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.47/0.70         (((k2_relset_1 @ X42 @ X43 @ X41) = (k2_relat_1 @ X41))
% 0.47/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.47/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.70  thf('25', plain,
% 0.47/0.70      (((k2_relset_1 @ sk_A @ sk_B_2 @ sk_C_5) = (k2_relat_1 @ sk_C_5))),
% 0.47/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.70  thf('26', plain,
% 0.47/0.70      (![X44 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X44 @ (k2_relat_1 @ sk_C_5))
% 0.47/0.70          | ~ (m1_subset_1 @ X44 @ sk_B_2))),
% 0.47/0.70      inference('demod', [status(thm)], ['22', '25'])).
% 0.47/0.70  thf('27', plain,
% 0.47/0.70      ((((sk_C_5) = (k1_xboole_0))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_5)
% 0.47/0.70        | ~ (m1_subset_1 @ (sk_C_4 @ sk_C_5) @ sk_B_2))),
% 0.47/0.70      inference('sup-', [status(thm)], ['21', '26'])).
% 0.47/0.70  thf('28', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(cc2_relat_1, axiom,
% 0.47/0.70    (![A:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ A ) =>
% 0.47/0.70       ( ![B:$i]:
% 0.47/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.70  thf('29', plain,
% 0.47/0.70      (![X12 : $i, X13 : $i]:
% 0.47/0.70         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.47/0.70          | (v1_relat_1 @ X12)
% 0.47/0.70          | ~ (v1_relat_1 @ X13))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.70  thf('30', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_C_5))),
% 0.47/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.70  thf(fc6_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.70  thf('31', plain,
% 0.47/0.70      (![X30 : $i, X31 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X30 @ X31))),
% 0.47/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.70  thf('32', plain, ((v1_relat_1 @ sk_C_5)),
% 0.47/0.70      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.70  thf('33', plain,
% 0.47/0.70      ((((sk_C_5) = (k1_xboole_0))
% 0.47/0.70        | ~ (m1_subset_1 @ (sk_C_4 @ sk_C_5) @ sk_B_2))),
% 0.47/0.70      inference('demod', [status(thm)], ['27', '32'])).
% 0.47/0.70  thf('34', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         (~ (v1_relat_1 @ X0)
% 0.47/0.70          | ((X0) = (k1_xboole_0))
% 0.47/0.70          | (r2_hidden @ (sk_C_4 @ X0) @ (k2_relat_1 @ X0)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['18', '20'])).
% 0.47/0.70  thf('35', plain,
% 0.47/0.70      ((m1_subset_1 @ sk_C_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.47/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.70  thf(cc2_relset_1, axiom,
% 0.47/0.70    (![A:$i,B:$i,C:$i]:
% 0.47/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.70  thf('36', plain,
% 0.47/0.70      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.47/0.70         ((v5_relat_1 @ X35 @ X37)
% 0.47/0.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37))))),
% 0.47/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.70  thf('37', plain, ((v5_relat_1 @ sk_C_5 @ sk_B_2)),
% 0.47/0.70      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.70  thf(d19_relat_1, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( v1_relat_1 @ B ) =>
% 0.47/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.70  thf('38', plain,
% 0.47/0.70      (![X14 : $i, X15 : $i]:
% 0.47/0.70         (~ (v5_relat_1 @ X14 @ X15)
% 0.47/0.70          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 0.47/0.70          | ~ (v1_relat_1 @ X14))),
% 0.47/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.47/0.70  thf('39', plain,
% 0.47/0.70      ((~ (v1_relat_1 @ sk_C_5) | (r1_tarski @ (k2_relat_1 @ sk_C_5) @ sk_B_2))),
% 0.47/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.47/0.70  thf('40', plain, ((v1_relat_1 @ sk_C_5)),
% 0.47/0.70      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.70  thf('41', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_5) @ sk_B_2)),
% 0.47/0.70      inference('demod', [status(thm)], ['39', '40'])).
% 0.47/0.70  thf(d3_tarski, axiom,
% 0.47/0.70    (![A:$i,B:$i]:
% 0.47/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.70  thf('42', plain,
% 0.47/0.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.47/0.70         (~ (r2_hidden @ X3 @ X4)
% 0.47/0.70          | (r2_hidden @ X3 @ X5)
% 0.47/0.70          | ~ (r1_tarski @ X4 @ X5))),
% 0.47/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.70  thf('43', plain,
% 0.47/0.70      (![X0 : $i]:
% 0.47/0.70         ((r2_hidden @ X0 @ sk_B_2)
% 0.47/0.70          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_5)))),
% 0.47/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.70  thf('44', plain,
% 0.47/0.70      ((((sk_C_5) = (k1_xboole_0))
% 0.47/0.70        | ~ (v1_relat_1 @ sk_C_5)
% 0.47/0.70        | (r2_hidden @ (sk_C_4 @ sk_C_5) @ sk_B_2))),
% 0.47/0.70      inference('sup-', [status(thm)], ['34', '43'])).
% 0.47/0.70  thf('45', plain, ((v1_relat_1 @ sk_C_5)),
% 0.47/0.70      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.70  thf('46', plain,
% 0.47/0.70      ((((sk_C_5) = (k1_xboole_0)) | (r2_hidden @ (sk_C_4 @ sk_C_5) @ sk_B_2))),
% 0.47/0.70      inference('demod', [status(thm)], ['44', '45'])).
% 0.47/0.70  thf(t1_subset, axiom,
% 0.47/0.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.47/0.70  thf('47', plain,
% 0.47/0.70      (![X10 : $i, X11 : $i]:
% 0.47/0.70         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.47/0.70      inference('cnf', [status(esa)], [t1_subset])).
% 0.47/0.70  thf('48', plain,
% 0.47/0.70      ((((sk_C_5) = (k1_xboole_0)) | (m1_subset_1 @ (sk_C_4 @ sk_C_5) @ sk_B_2))),
% 0.47/0.70      inference('sup-', [status(thm)], ['46', '47'])).
% 0.47/0.70  thf('49', plain, (((sk_C_5) = (k1_xboole_0))),
% 0.47/0.70      inference('clc', [status(thm)], ['33', '48'])).
% 0.47/0.70  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.70      inference('sup-', [status(thm)], ['12', '15'])).
% 0.47/0.70  thf('51', plain, ($false),
% 0.47/0.70      inference('demod', [status(thm)], ['17', '49', '50'])).
% 0.47/0.70  
% 0.47/0.70  % SZS output end Refutation
% 0.47/0.70  
% 0.47/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqOnxcwUFJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 104 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  588 (1140 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t22_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
        <=> ( ( k1_relset_1 @ B @ A @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_relset_1])).

thf('0',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B ) @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ sk_C_2 ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['17','20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ! [X26: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X26 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('27',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      & ! [X26: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X26 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ~ ! [X26: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X26 @ ( sk_E @ X26 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X26 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X25: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ! [X25: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('36',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('39',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X13 @ ( sk_D_1 @ X13 @ X11 ) ) @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ sk_C_2 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ! [X25: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_2 )
   <= ! [X25: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['32'])).

thf('43',plain,
    ( ~ ! [X25: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X25 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','31','33','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fqOnxcwUFJ
% 0.12/0.36  % Computer   : n013.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 11:17:55 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 80 iterations in 0.058s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.22/0.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(sk_E_type, type, sk_E: $i > $i).
% 0.22/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(t22_relset_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.53       ( ( ![D:$i]:
% 0.22/0.53           ( ~( ( r2_hidden @ D @ B ) & 
% 0.22/0.53                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.22/0.53         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.53        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.53          ( ( ![D:$i]:
% 0.22/0.53              ( ~( ( r2_hidden @ D @ B ) & 
% 0.22/0.53                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.22/0.53            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.22/0.53        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.22/0.53       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X26 : $i]:
% 0.22/0.53         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))
% 0.22/0.53          | (r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.53          | ~ (r2_hidden @ X26 @ sk_B))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      ((![X26 : $i]:
% 0.22/0.53          ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.53           | ~ (r2_hidden @ X26 @ sk_B))) | 
% 0.22/0.53       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.22/0.53      inference('split', [status(esa)], ['2'])).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X1 : $i, X3 : $i]:
% 0.22/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      ((![X26 : $i]:
% 0.22/0.53          ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.53           | ~ (r2_hidden @ X26 @ sk_B)))
% 0.22/0.53         <= ((![X26 : $i]:
% 0.22/0.53                ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.53                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.53      inference('split', [status(esa)], ['2'])).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((r1_tarski @ sk_B @ X0)
% 0.22/0.53           | (r2_hidden @ 
% 0.22/0.53              (k4_tarski @ (sk_C @ X0 @ sk_B) @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.22/0.53              sk_C_2)))
% 0.22/0.53         <= ((![X26 : $i]:
% 0.22/0.53                ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.53                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf(d4_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.53       ( ![C:$i]:
% 0.22/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.53         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.22/0.53          | (r2_hidden @ X9 @ X12)
% 0.22/0.53          | ((X12) != (k1_relat_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.54         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.22/0.54          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.22/0.54      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          ((r1_tarski @ sk_B @ X0)
% 0.22/0.54           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_relat_1 @ sk_C_2))))
% 0.22/0.54         <= ((![X26 : $i]:
% 0.22/0.54                ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.54                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X1 : $i, X3 : $i]:
% 0.22/0.54         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      ((((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))
% 0.22/0.54         | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))))
% 0.22/0.54         <= ((![X26 : $i]:
% 0.22/0.54                ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.54                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (((r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2)))
% 0.22/0.54         <= ((![X26 : $i]:
% 0.22/0.54                ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.54                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.54         ((v4_relat_1 @ X19 @ X20)
% 0.22/0.54          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('15', plain, ((v4_relat_1 @ sk_C_2 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf(d18_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X7 : $i, X8 : $i]:
% 0.22/0.54         (~ (v4_relat_1 @ X7 @ X8)
% 0.22/0.54          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.22/0.54          | ~ (v1_relat_1 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( v1_relat_1 @ C ) ))).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X16)
% 0.22/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('20', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.54  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['17', '20'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X4 : $i, X6 : $i]:
% 0.22/0.54         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_C_2))
% 0.22/0.54        | ((sk_B) = (k1_relat_1 @ sk_C_2)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      ((((sk_B) = (k1_relat_1 @ sk_C_2)))
% 0.22/0.54         <= ((![X26 : $i]:
% 0.22/0.54                ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.54                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.54         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.22/0.54          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B)))
% 0.22/0.54         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      ((((k1_relat_1 @ sk_C_2) != (sk_B)))
% 0.22/0.54         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      ((((sk_B) != (sk_B)))
% 0.22/0.54         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) & 
% 0.22/0.54             (![X26 : $i]:
% 0.22/0.54                ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.54                 | ~ (r2_hidden @ X26 @ sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['24', '29'])).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (~
% 0.22/0.54       (![X26 : $i]:
% 0.22/0.54          ((r2_hidden @ (k4_tarski @ X26 @ (sk_E @ X26)) @ sk_C_2)
% 0.22/0.54           | ~ (r2_hidden @ X26 @ sk_B))) | 
% 0.22/0.54       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X25 : $i]:
% 0.22/0.54         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.22/0.54          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_2))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      ((![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_2)) | 
% 0.22/0.54       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.22/0.54      inference('split', [status(esa)], ['32'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))
% 0.22/0.54         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.22/0.54      inference('split', [status(esa)], ['2'])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      ((((k1_relat_1 @ sk_C_2) = (sk_B)))
% 0.22/0.54         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.22/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X13 @ X12)
% 0.22/0.54          | (r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.22/0.54          | ((X12) != (k1_relat_1 @ X11)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X11 : $i, X13 : $i]:
% 0.22/0.54         ((r2_hidden @ (k4_tarski @ X13 @ (sk_D_1 @ X13 @ X11)) @ X11)
% 0.22/0.54          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (~ (r2_hidden @ X0 @ sk_B)
% 0.22/0.54           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_2)) @ sk_C_2)))
% 0.22/0.54         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['37', '39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_2)) @ sk_C_2))
% 0.22/0.54         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.22/0.54             (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['34', '40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_2))
% 0.22/0.54         <= ((![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_2)))),
% 0.22/0.54      inference('split', [status(esa)], ['32'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (~ (![X25 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X25) @ sk_C_2)) | 
% 0.22/0.54       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) | 
% 0.22/0.54       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf('44', plain, ($false),
% 0.22/0.54      inference('sat_resolution*', [status(thm)], ['1', '3', '31', '33', '43'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

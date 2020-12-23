%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eO1fBfRkP5

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 183 expanded)
%              Number of leaves         :   35 (  69 expanded)
%              Depth                    :   16
%              Number of atoms          :  580 (2139 expanded)
%              Number of equality atoms :   15 (  62 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X20 @ X21 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('24',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('28',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['27','30'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X36: $i] :
      ( ~ ( r2_hidden @ X36 @ sk_A )
      | ~ ( r2_hidden @ X36 @ sk_C_1 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('46',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ X24 )
      | ( X25
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,(
    v1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['26','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['12','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eO1fBfRkP5
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 160 iterations in 0.104s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(t115_funct_2, conjecture,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54       ( ![E:$i]:
% 0.22/0.54         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.54              ( ![F:$i]:
% 0.22/0.54                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.54                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.54            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54          ( ![E:$i]:
% 0.22/0.54            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.54                 ( ![F:$i]:
% 0.22/0.54                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.54                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.22/0.54          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.22/0.54           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.54  thf(t143_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ C ) =>
% 0.22/0.54       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.54         ( ?[D:$i]:
% 0.22/0.54           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.54             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.54             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.22/0.54          | (r2_hidden @ (sk_D @ X22 @ X20 @ X21) @ (k1_relat_1 @ X22))
% 0.22/0.54          | ~ (v1_relat_1 @ X22))),
% 0.22/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.54        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( v1_relat_1 @ C ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X26)
% 0.22/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '9'])).
% 0.22/0.54  thf(d1_xboole_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.54  thf('12', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.54         ((v4_relat_1 @ X29 @ X30)
% 0.22/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('15', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf(d18_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         (~ (v4_relat_1 @ X17 @ X18)
% 0.22/0.54          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.22/0.54          | ~ (v1_relat_1 @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.54  thf(d1_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (r1_tarski @ X3 @ X4)
% 0.22/0.54          | (r2_hidden @ X3 @ X5)
% 0.22/0.54          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i]:
% 0.22/0.54         ((r2_hidden @ X3 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X3 @ X4))),
% 0.22/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      ((r2_hidden @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['19', '21'])).
% 0.22/0.54  thf(t1_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf(cc1_subset_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.22/0.54          | (v1_xboole_0 @ X8)
% 0.22/0.54          | ~ (v1_xboole_0 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['6', '9'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf(t4_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X14 @ X15)
% 0.22/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.22/0.54          | (m1_subset_1 @ X14 @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X0 @ sk_A)
% 0.22/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.54  thf('31', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.54  thf(t2_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i]:
% 0.22/0.54         ((r2_hidden @ X12 @ X13)
% 0.22/0.54          | (v1_xboole_0 @ X13)
% 0.22/0.54          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (((v1_xboole_0 @ sk_A)
% 0.22/0.54        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      (![X36 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X36 @ sk_A)
% 0.22/0.54          | ~ (r2_hidden @ X36 @ sk_C_1)
% 0.22/0.54          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X36)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (((v1_xboole_0 @ sk_A)
% 0.22/0.54        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))
% 0.22/0.54        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.54  thf('36', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.54  thf('37', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.22/0.54          | (r2_hidden @ (sk_D @ X22 @ X20 @ X21) @ X20)
% 0.22/0.54          | ~ (v1_relat_1 @ X22))),
% 0.22/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.54        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.54  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('40', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      (((v1_xboole_0 @ sk_A)
% 0.22/0.54        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 0.22/0.54      inference('demod', [status(thm)], ['35', '40'])).
% 0.22/0.54  thf('42', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.22/0.54          | (r2_hidden @ (k4_tarski @ (sk_D @ X22 @ X20 @ X21) @ X21) @ X22)
% 0.22/0.54          | ~ (v1_relat_1 @ X22))),
% 0.22/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.54        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.22/0.54           sk_D_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.54  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.22/0.54        sk_D_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.54  thf(t8_funct_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.54       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.54         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.54           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.54         (~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ X24)
% 0.22/0.54          | ((X25) = (k1_funct_1 @ X24 @ X23))
% 0.22/0.54          | ~ (v1_funct_1 @ X24)
% 0.22/0.54          | ~ (v1_relat_1 @ X24))),
% 0.22/0.54      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.54        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.54  thf('49', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('50', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E)))),
% 0.22/0.54      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.22/0.54  thf('52', plain, (((v1_xboole_0 @ sk_A) | ((sk_E) != (sk_E)))),
% 0.22/0.54      inference('demod', [status(thm)], ['41', '51'])).
% 0.22/0.54  thf('53', plain, ((v1_xboole_0 @ sk_A)),
% 0.22/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.22/0.54  thf('54', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['26', '53'])).
% 0.22/0.54  thf('55', plain, ($false), inference('demod', [status(thm)], ['12', '54'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.40/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

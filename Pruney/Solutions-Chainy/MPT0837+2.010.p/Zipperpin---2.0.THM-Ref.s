%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R1iQbkehHx

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:55 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 143 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :  652 (1875 expanded)
%              Number of equality atoms :   11 (  26 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,
    ( ( m1_subset_1 @ sk_E_2 @ sk_B )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_E_2 @ sk_B )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_2 ) @ sk_C )
      | ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_2 ) @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k7_relset_1 @ X23 @ X24 @ X25 @ X23 )
        = ( k2_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('6',plain,
    ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_D_2 ) @ sk_D_2 ) @ sk_C ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_C @ sk_B @ sk_D_2 ) @ sk_D_2 ) @ sk_C )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_2 ) @ sk_C ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_2 ) @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_D_2 ) @ sk_B )
   <= ( ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_2 ) @ sk_C ) )
      & ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['10','12'])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D_1 @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_D_2 ) @ sk_B ) )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_D_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_D_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_2 ) @ sk_C ) )
    | ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['11'])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_E_2 @ sk_B )
   <= ( m1_subset_1 @ sk_E_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ sk_E_2 @ sk_B ) )
   <= ( m1_subset_1 @ sk_E_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_E_2 @ sk_B )
   <= ( m1_subset_1 @ sk_E_2 @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X8: $i,X10: $i,X11: $i] :
      ( ( X8
       != ( k9_relat_1 @ X6 @ X5 ) )
      | ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X10 ) @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('38',plain,(
    ! [X5: $i,X6: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X11 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X10 ) @ X6 )
      | ( r2_hidden @ X10 @ ( k9_relat_1 @ X6 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_2 @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_E_2 @ X0 )
        | ~ ( v1_relat_1 @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['16','17'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_2 @ ( k9_relat_1 @ sk_C @ X0 ) )
        | ~ ( r2_hidden @ sk_E_2 @ X0 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_2 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ( ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C )
      & ( m1_subset_1 @ sk_E_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,
    ( ( k9_relat_1 @ sk_C @ sk_B )
    = ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_D_2 @ ( k9_relat_1 @ sk_C @ sk_B ) )
   <= ~ ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E_2 @ sk_D_2 ) @ sk_C )
    | ( r2_hidden @ sk_D_2 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_E_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','29','30','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R1iQbkehHx
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 152 iterations in 0.086s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.36/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.36/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.36/0.54  thf(t48_relset_1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.54           ( ![C:$i]:
% 0.36/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.54               ( ![D:$i]:
% 0.36/0.54                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.36/0.54                   ( ?[E:$i]:
% 0.36/0.54                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.36/0.54                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.36/0.54          ( ![B:$i]:
% 0.36/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.36/0.54              ( ![C:$i]:
% 0.36/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.54                  ( ![D:$i]:
% 0.36/0.54                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.36/0.54                      ( ?[E:$i]:
% 0.36/0.54                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.36/0.54                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (((m1_subset_1 @ sk_E_2 @ sk_B)
% 0.36/0.54        | (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (((m1_subset_1 @ sk_E_2 @ sk_B)) | 
% 0.36/0.54       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X26 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X26 @ sk_B)
% 0.36/0.54          | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_2) @ sk_C)
% 0.36/0.54          | ~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      ((![X26 : $i]:
% 0.36/0.54          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.36/0.54           | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_2) @ sk_C))) | 
% 0.36/0.54       ~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t38_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.36/0.54         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.54         (((k7_relset_1 @ X23 @ X24 @ X25 @ X23)
% 0.36/0.54            = (k2_relset_1 @ X23 @ X24 @ X25))
% 0.36/0.54          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.36/0.54      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((k7_relset_1 @ sk_B @ sk_A @ sk_C @ sk_B)
% 0.36/0.54         = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.36/0.54          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k7_relset_1 @ sk_B @ sk_A @ sk_C @ X0) = (k9_relat_1 @ sk_C @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (((k9_relat_1 @ sk_C @ sk_B) = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['6', '9'])).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C)
% 0.36/0.54        | (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('split', [status(esa)], ['11'])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (((r2_hidden @ sk_D_2 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('sup+', [status(thm)], ['10', '12'])).
% 0.36/0.54  thf(t143_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ C ) =>
% 0.36/0.54       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.36/0.54         ( ?[D:$i]:
% 0.36/0.54           ( ( r2_hidden @ D @ B ) & 
% 0.36/0.54             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.36/0.54             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.36/0.54          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X15 @ X13 @ X14) @ X14) @ X15)
% 0.36/0.54          | ~ (v1_relat_1 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (((~ (v1_relat_1 @ sk_C)
% 0.36/0.54         | (r2_hidden @ 
% 0.36/0.54            (k4_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_D_2) @ sk_D_2) @ sk_C)))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('16', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc1_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( v1_relat_1 @ C ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.54         ((v1_relat_1 @ X16)
% 0.36/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.54  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_C @ sk_B @ sk_D_2) @ sk_D_2) @ 
% 0.36/0.54         sk_C))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['15', '18'])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      ((![X26 : $i]:
% 0.36/0.54          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.36/0.54           | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_2) @ sk_C)))
% 0.36/0.54         <= ((![X26 : $i]:
% 0.36/0.54                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.36/0.54                 | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_2) @ sk_C))))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((~ (m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_D_2) @ sk_B))
% 0.36/0.54         <= ((![X26 : $i]:
% 0.36/0.54                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.36/0.54                 | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_2) @ sk_C))) & 
% 0.36/0.54             ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (((r2_hidden @ sk_D_2 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('sup+', [status(thm)], ['10', '12'])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.36/0.54          | (r2_hidden @ (sk_D_1 @ X15 @ X13 @ X14) @ X13)
% 0.36/0.54          | ~ (v1_relat_1 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (((~ (v1_relat_1 @ sk_C)
% 0.36/0.54         | (r2_hidden @ (sk_D_1 @ sk_C @ sk_B @ sk_D_2) @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.54  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('26', plain,
% 0.36/0.54      (((r2_hidden @ (sk_D_1 @ sk_C @ sk_B @ sk_D_2) @ sk_B))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.36/0.54  thf(t1_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (((m1_subset_1 @ (sk_D_1 @ sk_C @ sk_B @ sk_D_2) @ sk_B))
% 0.36/0.54         <= (((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (~
% 0.36/0.54       (![X26 : $i]:
% 0.36/0.54          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.36/0.54           | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_2) @ sk_C))) | 
% 0.36/0.54       ~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '28'])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C)) | 
% 0.36/0.54       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))),
% 0.36/0.54      inference('split', [status(esa)], ['11'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (((m1_subset_1 @ sk_E_2 @ sk_B)) <= (((m1_subset_1 @ sk_E_2 @ sk_B)))),
% 0.36/0.54      inference('split', [status(esa)], ['0'])).
% 0.36/0.54  thf(t2_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]:
% 0.36/0.54         ((r2_hidden @ X2 @ X3)
% 0.36/0.54          | (v1_xboole_0 @ X3)
% 0.36/0.54          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.36/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      ((((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_E_2 @ sk_B)))
% 0.36/0.54         <= (((m1_subset_1 @ sk_E_2 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.54  thf('34', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (((r2_hidden @ sk_E_2 @ sk_B)) <= (((m1_subset_1 @ sk_E_2 @ sk_B)))),
% 0.36/0.54      inference('clc', [status(thm)], ['33', '34'])).
% 0.36/0.54  thf('36', plain,
% 0.36/0.54      (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C))
% 0.36/0.54         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C)))),
% 0.36/0.54      inference('split', [status(esa)], ['11'])).
% 0.36/0.54  thf(d13_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i,C:$i]:
% 0.36/0.54         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.36/0.54           ( ![D:$i]:
% 0.36/0.54             ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.54               ( ?[E:$i]:
% 0.36/0.54                 ( ( r2_hidden @ E @ B ) & 
% 0.36/0.54                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i, X8 : $i, X10 : $i, X11 : $i]:
% 0.36/0.54         (((X8) != (k9_relat_1 @ X6 @ X5))
% 0.36/0.54          | (r2_hidden @ X10 @ X8)
% 0.36/0.54          | ~ (r2_hidden @ (k4_tarski @ X11 @ X10) @ X6)
% 0.36/0.54          | ~ (r2_hidden @ X11 @ X5)
% 0.36/0.54          | ~ (v1_relat_1 @ X6))),
% 0.36/0.54      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      (![X5 : $i, X6 : $i, X10 : $i, X11 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X6)
% 0.36/0.54          | ~ (r2_hidden @ X11 @ X5)
% 0.36/0.54          | ~ (r2_hidden @ (k4_tarski @ X11 @ X10) @ X6)
% 0.36/0.54          | (r2_hidden @ X10 @ (k9_relat_1 @ X6 @ X5)))),
% 0.36/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.36/0.54  thf('39', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          ((r2_hidden @ sk_D_2 @ (k9_relat_1 @ sk_C @ X0))
% 0.36/0.54           | ~ (r2_hidden @ sk_E_2 @ X0)
% 0.36/0.54           | ~ (v1_relat_1 @ sk_C)))
% 0.36/0.54         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '38'])).
% 0.36/0.54  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('41', plain,
% 0.36/0.54      ((![X0 : $i]:
% 0.36/0.54          ((r2_hidden @ sk_D_2 @ (k9_relat_1 @ sk_C @ X0))
% 0.36/0.54           | ~ (r2_hidden @ sk_E_2 @ X0)))
% 0.36/0.54         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (((r2_hidden @ sk_D_2 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.36/0.54         <= (((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C)) & 
% 0.36/0.54             ((m1_subset_1 @ sk_E_2 @ sk_B)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['35', '41'])).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (((k9_relat_1 @ sk_C @ sk_B) = (k2_relset_1 @ sk_B @ sk_A @ sk_C))),
% 0.36/0.54      inference('demod', [status(thm)], ['6', '9'])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('split', [status(esa)], ['2'])).
% 0.36/0.54  thf('45', plain,
% 0.36/0.54      ((~ (r2_hidden @ sk_D_2 @ (k9_relat_1 @ sk_C @ sk_B)))
% 0.36/0.54         <= (~ ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (~ ((r2_hidden @ (k4_tarski @ sk_E_2 @ sk_D_2) @ sk_C)) | 
% 0.36/0.54       ((r2_hidden @ sk_D_2 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C))) | 
% 0.36/0.54       ~ ((m1_subset_1 @ sk_E_2 @ sk_B))),
% 0.36/0.54      inference('sup-', [status(thm)], ['42', '45'])).
% 0.36/0.54  thf('47', plain, ($false),
% 0.36/0.54      inference('sat_resolution*', [status(thm)], ['1', '3', '29', '30', '46'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

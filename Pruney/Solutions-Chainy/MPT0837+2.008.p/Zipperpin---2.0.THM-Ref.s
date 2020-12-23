%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hpAq93StxD

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 154 expanded)
%              Number of leaves         :   29 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  589 (1772 expanded)
%              Number of equality atoms :   15 (  27 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('0',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_3 ) @ sk_C_1 )
      | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('15',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['12','15'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ X0 ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_3 ) @ sk_C_1 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_3 ) @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_3 ) @ sk_C_1 ) )
      & ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D_2 @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3 ) @ sk_B )
   <= ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X26 @ sk_D_3 ) @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_relat_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k2_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_D_3 @ ( k2_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_3 ) @ sk_C_1 )
    | ( r2_hidden @ sk_D_3 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','37','38','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hpAq93StxD
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:59:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 64 iterations in 0.025s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.47  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.19/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(t48_relset_1, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47           ( ![C:$i]:
% 0.19/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.47               ( ![D:$i]:
% 0.19/0.47                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.19/0.47                   ( ?[E:$i]:
% 0.19/0.47                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.19/0.47                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.47              ( ![C:$i]:
% 0.19/0.47                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.47                  ( ![D:$i]:
% 0.19/0.47                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.19/0.47                      ( ?[E:$i]:
% 0.19/0.47                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.19/0.47                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X26 : $i]:
% 0.19/0.47         (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.47          | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_3) @ sk_C_1)
% 0.19/0.47          | ~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((![X26 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.47           | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_3) @ sk_C_1))) | 
% 0.19/0.47       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.47         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.19/0.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)
% 0.19/0.47        | (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('split', [status(esa)], ['5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['4', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc2_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.47         ((v4_relat_1 @ X20 @ X21)
% 0.19/0.47          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.47  thf('10', plain, ((v4_relat_1 @ sk_C_1 @ sk_B)),
% 0.19/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf(t209_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.47       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X15 : $i, X16 : $i]:
% 0.19/0.47         (((X15) = (k7_relat_1 @ X15 @ X16))
% 0.19/0.47          | ~ (v4_relat_1 @ X15 @ X16)
% 0.19/0.47          | ~ (v1_relat_1 @ X15))),
% 0.19/0.47      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ sk_C_1) | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(cc1_relset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.47       ( v1_relat_1 @ C ) ))).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.47         ((v1_relat_1 @ X17)
% 0.19/0.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.47  thf('15', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['12', '15'])).
% 0.19/0.47  thf(t148_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ B ) =>
% 0.19/0.47       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (![X13 : $i, X14 : $i]:
% 0.19/0.47         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.19/0.47          | ~ (v1_relat_1 @ X13))),
% 0.19/0.47      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))
% 0.19/0.47        | ~ (v1_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf('19', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('20', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf(t143_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( v1_relat_1 @ C ) =>
% 0.19/0.47       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.19/0.47         ( ?[D:$i]:
% 0.19/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.47             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.19/0.47             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.19/0.47          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.19/0.47          | ~ (v1_relat_1 @ X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.19/0.47          | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.47          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.19/0.47             sk_C_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.19/0.47          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ X0) @ 
% 0.19/0.47             sk_C_1))),
% 0.19/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      (((r2_hidden @ 
% 0.19/0.47         (k4_tarski @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_D_3) @ sk_C_1))
% 0.19/0.47         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['7', '24'])).
% 0.19/0.47  thf('26', plain,
% 0.19/0.47      ((![X26 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.47           | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_3) @ sk_C_1)))
% 0.19/0.47         <= ((![X26 : $i]:
% 0.19/0.47                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.47                 | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_3) @ sk_C_1))))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('27', plain,
% 0.19/0.47      ((~ (m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.19/0.47         <= ((![X26 : $i]:
% 0.19/0.47                (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.47                 | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_3) @ sk_C_1))) & 
% 0.19/0.47             ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.47  thf('28', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.47         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('sup+', [status(thm)], ['4', '6'])).
% 0.19/0.47  thf('29', plain, (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf('30', plain,
% 0.19/0.47      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.19/0.47          | (r2_hidden @ (sk_D_2 @ X12 @ X10 @ X11) @ X10)
% 0.19/0.47          | ~ (v1_relat_1 @ X12))),
% 0.19/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.19/0.47          | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.47          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.19/0.47      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.47  thf('32', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1))
% 0.19/0.47          | (r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ X0) @ sk_B))),
% 0.19/0.47      inference('demod', [status(thm)], ['31', '32'])).
% 0.19/0.47  thf('34', plain,
% 0.19/0.47      (((r2_hidden @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.19/0.47         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['28', '33'])).
% 0.19/0.47  thf(t1_subset, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.47  thf('36', plain,
% 0.19/0.47      (((m1_subset_1 @ (sk_D_2 @ sk_C_1 @ sk_B @ sk_D_3) @ sk_B))
% 0.19/0.47         <= (((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      (~
% 0.19/0.47       (![X26 : $i]:
% 0.19/0.47          (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.47           | ~ (r2_hidden @ (k4_tarski @ X26 @ sk_D_3) @ sk_C_1))) | 
% 0.19/0.47       ~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.47      inference('demod', [status(thm)], ['27', '36'])).
% 0.19/0.47  thf('38', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.19/0.47       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.47      inference('split', [status(esa)], ['5'])).
% 0.19/0.47  thf('39', plain,
% 0.19/0.47      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.19/0.47      inference('split', [status(esa)], ['5'])).
% 0.19/0.47  thf(d5_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.19/0.47       ( ![C:$i]:
% 0.19/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.47           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.19/0.47  thf('40', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.47         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4)
% 0.19/0.47          | (r2_hidden @ X3 @ X5)
% 0.19/0.47          | ((X5) != (k2_relat_1 @ X4)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.47  thf('41', plain,
% 0.19/0.47      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.47         ((r2_hidden @ X3 @ (k2_relat_1 @ X4))
% 0.19/0.47          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.19/0.47      inference('simplify', [status(thm)], ['40'])).
% 0.19/0.47  thf('42', plain,
% 0.19/0.47      (((r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.47         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['39', '41'])).
% 0.19/0.47  thf('43', plain,
% 0.19/0.47      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('44', plain,
% 0.19/0.47      ((~ (r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))
% 0.19/0.47         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('split', [status(esa)], ['0'])).
% 0.19/0.47  thf('45', plain,
% 0.19/0.47      ((~ (r2_hidden @ sk_D_3 @ (k2_relat_1 @ sk_C_1)))
% 0.19/0.47         <= (~ ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.19/0.47  thf('46', plain,
% 0.19/0.47      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_3) @ sk_C_1)) | 
% 0.19/0.47       ((r2_hidden @ sk_D_3 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['42', '45'])).
% 0.19/0.47  thf('47', plain, ($false),
% 0.19/0.47      inference('sat_resolution*', [status(thm)], ['1', '37', '38', '46'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

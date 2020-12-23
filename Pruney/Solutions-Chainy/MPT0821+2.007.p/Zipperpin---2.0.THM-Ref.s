%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mdSH6oGdBn

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:56 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 117 expanded)
%              Number of leaves         :   25 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  674 (1277 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
     != sk_B_1 )
    | ( r2_hidden @ sk_D_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B_1 )
    | ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
     != sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X31: $i] :
      ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
        = sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
      | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) )
    | ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
      = sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X24 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r1_tarski @ X13 @ X11 )
      | ( X12
       != ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['19','22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) )
   <= ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_B_1 ) @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) ) @ sk_C_3 ) )
   <= ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X19 )
      | ( r2_hidden @ X17 @ X20 )
      | ( X20
       != ( k1_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X17 @ ( k1_relat_1 @ X19 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X18 ) @ X19 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k1_relat_1 @ sk_C_3 ) ) )
   <= ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,
    ( ( ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ sk_C_3 ) )
      | ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ sk_C_3 ) ) )
   <= ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k1_relat_1 @ sk_C_3 ) )
   <= ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,
    ( ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 )
      | ( ( k1_relat_1 @ sk_C_3 )
        = sk_B_1 ) )
   <= ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
      = sk_B_1 )
   <= ! [X31: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
        | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('37',plain,
    ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
     != sk_B_1 )
   <= ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
     != sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
     != sk_B_1 )
   <= ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
     != sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
       != sk_B_1 )
      & ! [X31: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
          | ~ ( r2_hidden @ X31 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ~ ! [X31: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X31 @ ( sk_E @ X31 ) ) @ sk_C_3 )
          | ~ ( r2_hidden @ X31 @ sk_B_1 ) )
    | ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X30: $i] :
      ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
       != sk_B_1 )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X30 ) @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ! [X30: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X30 ) @ sk_C_3 )
    | ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
     != sk_B_1 ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B_1 )
   <= ( r2_hidden @ sk_D_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('45',plain,
    ( ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
      = sk_B_1 )
   <= ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
      = sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_C_3 )
      = sk_B_1 )
   <= ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_1 @ X21 @ X19 ) ) @ X19 )
      | ( X20
       != ( k1_relat_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('48',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ ( sk_D_1 @ X21 @ X19 ) ) @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B_1 )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_3 ) ) @ sk_C_3 ) )
   <= ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_3 ) ) @ sk_C_3 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B_1 )
      & ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
        = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,
    ( ! [X30: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X30 ) @ sk_C_3 )
   <= ! [X30: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X30 ) @ sk_C_3 ) ),
    inference(split,[status(esa)],['41'])).

thf('52',plain,
    ( ~ ! [X30: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X30 ) @ sk_C_3 )
    | ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
     != sk_B_1 )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','40','42','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mdSH6oGdBn
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.72  % Solved by: fo/fo7.sh
% 0.52/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.72  % done 364 iterations in 0.263s
% 0.52/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.72  % SZS output start Refutation
% 0.52/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.72  thf(sk_E_type, type, sk_E: $i > $i).
% 0.52/0.72  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.52/0.72  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.52/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.52/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.72  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.52/0.72  thf(t22_relset_1, conjecture,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.52/0.72       ( ( ![D:$i]:
% 0.52/0.72           ( ~( ( r2_hidden @ D @ B ) & 
% 0.52/0.72                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.52/0.72         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.52/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.72        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.52/0.72          ( ( ![D:$i]:
% 0.52/0.72              ( ~( ( r2_hidden @ D @ B ) & 
% 0.52/0.72                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.52/0.72            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 0.52/0.72    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 0.52/0.72  thf('0', plain,
% 0.52/0.72      ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) != (sk_B_1))
% 0.52/0.72        | (r2_hidden @ sk_D_2 @ sk_B_1))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('1', plain,
% 0.52/0.72      (((r2_hidden @ sk_D_2 @ sk_B_1)) | 
% 0.52/0.72       ~ (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1)))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('2', plain,
% 0.52/0.72      (![X31 : $i]:
% 0.52/0.72         (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))
% 0.52/0.72          | (r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72          | ~ (r2_hidden @ X31 @ sk_B_1))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('3', plain,
% 0.52/0.72      ((![X31 : $i]:
% 0.52/0.72          ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72           | ~ (r2_hidden @ X31 @ sk_B_1))) | 
% 0.52/0.72       (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1)))),
% 0.52/0.72      inference('split', [status(esa)], ['2'])).
% 0.52/0.72  thf('4', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(dt_k1_relset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.72       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.52/0.72  thf('5', plain,
% 0.52/0.72      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.52/0.72         ((m1_subset_1 @ (k1_relset_1 @ X24 @ X25 @ X26) @ (k1_zfmisc_1 @ X24))
% 0.52/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.52/0.72      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.52/0.72  thf('6', plain,
% 0.52/0.72      ((m1_subset_1 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) @ 
% 0.52/0.72        (k1_zfmisc_1 @ sk_B_1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.72  thf(t2_subset, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ A @ B ) =>
% 0.52/0.72       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.52/0.72  thf('7', plain,
% 0.52/0.72      (![X15 : $i, X16 : $i]:
% 0.52/0.72         ((r2_hidden @ X15 @ X16)
% 0.52/0.72          | (v1_xboole_0 @ X16)
% 0.52/0.72          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.52/0.72      inference('cnf', [status(esa)], [t2_subset])).
% 0.52/0.72  thf('8', plain,
% 0.52/0.72      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.52/0.72        | (r2_hidden @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) @ 
% 0.52/0.72           (k1_zfmisc_1 @ sk_B_1)))),
% 0.52/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.72  thf(d10_xboole_0, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.72  thf('9', plain,
% 0.52/0.72      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.72  thf('10', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.52/0.72      inference('simplify', [status(thm)], ['9'])).
% 0.52/0.72  thf(d1_zfmisc_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.52/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.52/0.72  thf('11', plain,
% 0.52/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.72         (~ (r1_tarski @ X10 @ X11)
% 0.52/0.72          | (r2_hidden @ X10 @ X12)
% 0.52/0.72          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.52/0.72  thf('12', plain,
% 0.52/0.72      (![X10 : $i, X11 : $i]:
% 0.52/0.72         ((r2_hidden @ X10 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X10 @ X11))),
% 0.52/0.72      inference('simplify', [status(thm)], ['11'])).
% 0.52/0.72  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['10', '12'])).
% 0.52/0.72  thf(d1_xboole_0, axiom,
% 0.52/0.72    (![A:$i]:
% 0.52/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.72  thf('14', plain,
% 0.52/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.72  thf('15', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.72  thf('16', plain,
% 0.52/0.72      ((r2_hidden @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) @ 
% 0.52/0.72        (k1_zfmisc_1 @ sk_B_1))),
% 0.52/0.72      inference('clc', [status(thm)], ['8', '15'])).
% 0.52/0.72  thf('17', plain,
% 0.52/0.72      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X13 @ X12)
% 0.52/0.72          | (r1_tarski @ X13 @ X11)
% 0.52/0.72          | ((X12) != (k1_zfmisc_1 @ X11)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.52/0.72  thf('18', plain,
% 0.52/0.72      (![X11 : $i, X13 : $i]:
% 0.52/0.72         ((r1_tarski @ X13 @ X11) | ~ (r2_hidden @ X13 @ (k1_zfmisc_1 @ X11)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.52/0.72  thf('19', plain,
% 0.52/0.72      ((r1_tarski @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) @ sk_B_1)),
% 0.52/0.72      inference('sup-', [status(thm)], ['16', '18'])).
% 0.52/0.72  thf('20', plain,
% 0.52/0.72      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.52/0.72    (![A:$i,B:$i,C:$i]:
% 0.52/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.52/0.72  thf('21', plain,
% 0.52/0.72      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.52/0.72         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 0.52/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.52/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.52/0.72  thf('22', plain,
% 0.52/0.72      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.52/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.72  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1)),
% 0.52/0.72      inference('demod', [status(thm)], ['19', '22'])).
% 0.52/0.72  thf(d3_tarski, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.72  thf('24', plain,
% 0.52/0.72      (![X4 : $i, X6 : $i]:
% 0.52/0.72         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.52/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.72  thf('25', plain,
% 0.52/0.72      ((![X31 : $i]:
% 0.52/0.72          ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72           | ~ (r2_hidden @ X31 @ sk_B_1)))
% 0.52/0.72         <= ((![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('split', [status(esa)], ['2'])).
% 0.52/0.72  thf('26', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          ((r1_tarski @ sk_B_1 @ X0)
% 0.52/0.72           | (r2_hidden @ 
% 0.52/0.72              (k4_tarski @ (sk_C @ X0 @ sk_B_1) @ (sk_E @ (sk_C @ X0 @ sk_B_1))) @ 
% 0.52/0.72              sk_C_3)))
% 0.52/0.72         <= ((![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.52/0.72  thf(d4_relat_1, axiom,
% 0.52/0.72    (![A:$i,B:$i]:
% 0.52/0.72     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.52/0.72       ( ![C:$i]:
% 0.52/0.72         ( ( r2_hidden @ C @ B ) <=>
% 0.52/0.72           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.52/0.72  thf('27', plain,
% 0.52/0.72      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.72         (~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ X19)
% 0.52/0.72          | (r2_hidden @ X17 @ X20)
% 0.52/0.72          | ((X20) != (k1_relat_1 @ X19)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.72  thf('28', plain,
% 0.52/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.72         ((r2_hidden @ X17 @ (k1_relat_1 @ X19))
% 0.52/0.72          | ~ (r2_hidden @ (k4_tarski @ X17 @ X18) @ X19))),
% 0.52/0.72      inference('simplify', [status(thm)], ['27'])).
% 0.52/0.72  thf('29', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          ((r1_tarski @ sk_B_1 @ X0)
% 0.52/0.72           | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k1_relat_1 @ sk_C_3))))
% 0.52/0.72         <= ((![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['26', '28'])).
% 0.52/0.72  thf('30', plain,
% 0.52/0.72      (![X4 : $i, X6 : $i]:
% 0.52/0.72         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.52/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.72  thf('31', plain,
% 0.52/0.72      ((((r1_tarski @ sk_B_1 @ (k1_relat_1 @ sk_C_3))
% 0.52/0.72         | (r1_tarski @ sk_B_1 @ (k1_relat_1 @ sk_C_3))))
% 0.52/0.72         <= ((![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['29', '30'])).
% 0.52/0.72  thf('32', plain,
% 0.52/0.72      (((r1_tarski @ sk_B_1 @ (k1_relat_1 @ sk_C_3)))
% 0.52/0.72         <= ((![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('simplify', [status(thm)], ['31'])).
% 0.52/0.72  thf('33', plain,
% 0.52/0.72      (![X7 : $i, X9 : $i]:
% 0.52/0.72         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.52/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.72  thf('34', plain,
% 0.52/0.72      (((~ (r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1)
% 0.52/0.72         | ((k1_relat_1 @ sk_C_3) = (sk_B_1))))
% 0.52/0.72         <= ((![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.72  thf('35', plain,
% 0.52/0.72      ((((k1_relat_1 @ sk_C_3) = (sk_B_1)))
% 0.52/0.72         <= ((![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['23', '34'])).
% 0.52/0.72  thf('36', plain,
% 0.52/0.72      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.52/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.72  thf('37', plain,
% 0.52/0.72      ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) != (sk_B_1)))
% 0.52/0.72         <= (~ (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('38', plain,
% 0.52/0.72      ((((k1_relat_1 @ sk_C_3) != (sk_B_1)))
% 0.52/0.72         <= (~ (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.52/0.72  thf('39', plain,
% 0.52/0.72      ((((sk_B_1) != (sk_B_1)))
% 0.52/0.72         <= (~ (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))) & 
% 0.52/0.72             (![X31 : $i]:
% 0.52/0.72                ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72                 | ~ (r2_hidden @ X31 @ sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['35', '38'])).
% 0.52/0.72  thf('40', plain,
% 0.52/0.72      (~
% 0.52/0.72       (![X31 : $i]:
% 0.52/0.72          ((r2_hidden @ (k4_tarski @ X31 @ (sk_E @ X31)) @ sk_C_3)
% 0.52/0.72           | ~ (r2_hidden @ X31 @ sk_B_1))) | 
% 0.52/0.72       (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['39'])).
% 0.52/0.72  thf('41', plain,
% 0.52/0.72      (![X30 : $i]:
% 0.52/0.72         (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) != (sk_B_1))
% 0.52/0.72          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X30) @ sk_C_3))),
% 0.52/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.72  thf('42', plain,
% 0.52/0.72      ((![X30 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X30) @ sk_C_3)) | 
% 0.52/0.72       ~ (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1)))),
% 0.52/0.72      inference('split', [status(esa)], ['41'])).
% 0.52/0.72  thf('43', plain,
% 0.52/0.72      (((r2_hidden @ sk_D_2 @ sk_B_1)) <= (((r2_hidden @ sk_D_2 @ sk_B_1)))),
% 0.52/0.72      inference('split', [status(esa)], ['0'])).
% 0.52/0.72  thf('44', plain,
% 0.52/0.72      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.52/0.72      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.72  thf('45', plain,
% 0.52/0.72      ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1)))
% 0.52/0.72         <= ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))))),
% 0.52/0.72      inference('split', [status(esa)], ['2'])).
% 0.52/0.72  thf('46', plain,
% 0.52/0.72      ((((k1_relat_1 @ sk_C_3) = (sk_B_1)))
% 0.52/0.72         <= ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))))),
% 0.52/0.72      inference('sup+', [status(thm)], ['44', '45'])).
% 0.52/0.72  thf('47', plain,
% 0.52/0.72      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.52/0.72         (~ (r2_hidden @ X21 @ X20)
% 0.52/0.72          | (r2_hidden @ (k4_tarski @ X21 @ (sk_D_1 @ X21 @ X19)) @ X19)
% 0.52/0.72          | ((X20) != (k1_relat_1 @ X19)))),
% 0.52/0.72      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.72  thf('48', plain,
% 0.52/0.72      (![X19 : $i, X21 : $i]:
% 0.52/0.72         ((r2_hidden @ (k4_tarski @ X21 @ (sk_D_1 @ X21 @ X19)) @ X19)
% 0.52/0.72          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X19)))),
% 0.52/0.72      inference('simplify', [status(thm)], ['47'])).
% 0.52/0.72  thf('49', plain,
% 0.52/0.72      ((![X0 : $i]:
% 0.52/0.72          (~ (r2_hidden @ X0 @ sk_B_1)
% 0.52/0.72           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_3)) @ sk_C_3)))
% 0.52/0.72         <= ((((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['46', '48'])).
% 0.52/0.72  thf('50', plain,
% 0.52/0.72      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_3)) @ sk_C_3))
% 0.52/0.72         <= (((r2_hidden @ sk_D_2 @ sk_B_1)) & 
% 0.52/0.72             (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))))),
% 0.52/0.72      inference('sup-', [status(thm)], ['43', '49'])).
% 0.52/0.72  thf('51', plain,
% 0.52/0.72      ((![X30 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X30) @ sk_C_3))
% 0.52/0.72         <= ((![X30 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X30) @ sk_C_3)))),
% 0.52/0.72      inference('split', [status(esa)], ['41'])).
% 0.52/0.72  thf('52', plain,
% 0.52/0.72      (~ (![X30 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X30) @ sk_C_3)) | 
% 0.52/0.72       ~ (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (sk_B_1))) | 
% 0.52/0.72       ~ ((r2_hidden @ sk_D_2 @ sk_B_1))),
% 0.52/0.72      inference('sup-', [status(thm)], ['50', '51'])).
% 0.52/0.72  thf('53', plain, ($false),
% 0.52/0.72      inference('sat_resolution*', [status(thm)], ['1', '3', '40', '42', '52'])).
% 0.52/0.72  
% 0.52/0.72  % SZS output end Refutation
% 0.52/0.72  
% 0.52/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

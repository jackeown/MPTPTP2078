%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xTLDf9TGRy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 112 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  413 ( 709 expanded)
%              Number of equality atoms :   47 (  79 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
     => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ k1_xboole_0 @ A )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) )
       => ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X46 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X32 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ( k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','4'])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','9'])).

thf('14',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X32 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k8_relset_1 @ A @ B @ C @ D )
        = ( k10_relat_1 @ C @ D ) ) ) )).

thf('16',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k8_relset_1 @ X43 @ X44 @ X42 @ X45 )
        = ( k10_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2 )
        = ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
      = ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('20',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k10_relat_1 @ X39 @ X40 )
        = ( k10_relat_1 @ X39 @ ( k3_xboole_0 @ ( k2_relat_1 @ X39 ) @ X40 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = ( k10_relat_1 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_tarski @ X2 @ X1 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('29',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('30',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','28','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X41: $i] :
      ( ( ( k10_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('35',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['29','30'])).

thf('38',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','39'])).

thf('41',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['11','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xTLDf9TGRy
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:47:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 114 iterations in 0.038s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.50  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(t60_funct_2, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.22/0.50         ( m1_subset_1 @
% 0.22/0.50           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.22/0.50       ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ k1_xboole_0 @ A ) & 
% 0.22/0.50            ( m1_subset_1 @
% 0.22/0.50              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ A ) ) ) ) =>
% 0.22/0.50          ( ( k8_relset_1 @ k1_xboole_0 @ A @ C @ B ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t60_funct_2])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ sk_C @ sk_B_1) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t6_mcart_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.50                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.50                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.22/0.50                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.22/0.50                       ( r2_hidden @ G @ B ) ) =>
% 0.22/0.50                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X46 : $i]:
% 0.22/0.50         (((X46) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X46) @ X46))),
% 0.22/0.50      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t113_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X31 : $i, X32 : $i]:
% 0.22/0.50         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 0.22/0.50          | ((X31) != (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X32 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X32) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.50  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '4'])).
% 0.22/0.50  thf(t5_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.50          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X35 @ X36)
% 0.22/0.50          | ~ (v1_xboole_0 @ X37)
% 0.22/0.50          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.22/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.50  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.50  thf('9', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((k8_relset_1 @ k1_xboole_0 @ sk_A @ k1_xboole_0 @ sk_B_1)
% 0.22/0.50         != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '10'])).
% 0.22/0.50  thf('12', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['2', '4'])).
% 0.22/0.50  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '9'])).
% 0.22/0.50  thf('14', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X32 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X32) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.50  thf(redefinition_k8_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k8_relset_1 @ A @ B @ C @ D ) = ( k10_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.22/0.50          | ((k8_relset_1 @ X43 @ X44 @ X42 @ X45) = (k10_relat_1 @ X42 @ X45)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k8_relset_1])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.50          | ((k8_relset_1 @ k1_xboole_0 @ X0 @ X1 @ X2)
% 0.22/0.50              = (k10_relat_1 @ X1 @ X2)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0)
% 0.22/0.50           = (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.50  thf(t60_relat_1, axiom,
% 0.22/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('19', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf(t168_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( k10_relat_1 @ B @ A ) =
% 0.22/0.50         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X39 : $i, X40 : $i]:
% 0.22/0.50         (((k10_relat_1 @ X39 @ X40)
% 0.22/0.50            = (k10_relat_1 @ X39 @ (k3_xboole_0 @ (k2_relat_1 @ X39) @ X40)))
% 0.22/0.50          | ~ (v1_relat_1 @ X39))),
% 0.22/0.50      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.22/0.50            = (k10_relat_1 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.22/0.50          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf(commutativity_k2_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X1 : $i, X2 : $i]: ((k2_tarski @ X2 @ X1) = (k2_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.50  thf(t12_setfam_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X33 : $i, X34 : $i]:
% 0.22/0.50         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.22/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf(t2_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.50  thf('29', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.50  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.50  thf('30', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.50  thf('31', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.22/0.50           = (k10_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '28', '31'])).
% 0.22/0.50  thf('33', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf(t169_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X41 : $i]:
% 0.22/0.50         (((k10_relat_1 @ X41 @ (k2_relat_1 @ X41)) = (k1_relat_1 @ X41))
% 0.22/0.50          | ~ (v1_relat_1 @ X41))),
% 0.22/0.50      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.50        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.50      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.50  thf('36', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k8_relset_1 @ k1_xboole_0 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '39'])).
% 0.22/0.50  thf('41', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '40'])).
% 0.22/0.50  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

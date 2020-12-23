%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WALyqbzwv5

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:16 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 103 expanded)
%              Number of leaves         :   33 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  402 ( 583 expanded)
%              Number of equality atoms :   56 (  77 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t19_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t19_yellow_1])).

thf('0',plain,(
    ( k4_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('1',plain,(
    ! [X41: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X41 ) )
      = X41 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X62: $i] :
      ( ( k9_setfam_1 @ X62 )
      = ( k1_zfmisc_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    ! [X41: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X41 ) )
      = X41 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('4',plain,(
    ! [X63: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X63 ) @ X63 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X63 ) )
        = ( k3_tarski @ X63 ) )
      | ( v1_xboole_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = ( k3_tarski @ ( k9_setfam_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X64: $i] :
      ( ( k3_yellow_1 @ X64 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('7',plain,(
    ! [X41: $i] :
      ( ( k3_tarski @ ( k9_setfam_1 @ X41 ) )
      = X41 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ( r2_hidden @ X28 @ X30 )
      | ( X30
       != ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X62: $i] :
      ( ( k9_setfam_1 @ X62 )
      = ( k1_zfmisc_1 @ X62 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ ( k9_setfam_1 @ X29 ) )
      | ~ ( r1_tarski @ X28 @ X29 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X46 @ ( k1_relat_1 @ X45 ) )
      | ( ( k11_relat_1 @ X45 @ X46 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X48: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X48 ) )
      = X48 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X47: $i] :
      ( ( ( k1_relat_1 @ X47 )
       != k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X48: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('29',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','29'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_zfmisc_1 @ X39 @ X40 )
        = k1_xboole_0 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X39: $i] :
      ( ( k2_zfmisc_1 @ X39 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf(t203_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k11_relat_1 @ ( k2_zfmisc_1 @ B @ C ) @ A )
        = C ) ) )).

thf('34',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ( ( k11_relat_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) @ X42 )
        = X44 ) ) ),
    inference(cnf,[status(esa)],[t203_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k11_relat_1 @ ( k2_zfmisc_1 @ ( k9_setfam_1 @ X0 ) @ X1 ) @ X0 )
      = X1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['16','40'])).

thf('42',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WALyqbzwv5
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.16  % Solved by: fo/fo7.sh
% 0.89/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.16  % done 1322 iterations in 0.705s
% 0.89/1.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.16  % SZS output start Refutation
% 0.89/1.16  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.89/1.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.16  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.89/1.16  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.89/1.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.16  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.89/1.16  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.89/1.16  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.89/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.16  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.89/1.16  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.89/1.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.16  thf(t19_yellow_1, conjecture,
% 0.89/1.16    (![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ))).
% 0.89/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.16    (~( ![A:$i]: ( ( k4_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( A ) ) )),
% 0.89/1.16    inference('cnf.neg', [status(esa)], [t19_yellow_1])).
% 0.89/1.16  thf('0', plain, (((k4_yellow_0 @ (k3_yellow_1 @ sk_A)) != (sk_A))),
% 0.89/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.16  thf(t99_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.89/1.16  thf('1', plain, (![X41 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X41)) = (X41))),
% 0.89/1.16      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.89/1.16  thf(redefinition_k9_setfam_1, axiom,
% 0.89/1.16    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.89/1.16  thf('2', plain, (![X62 : $i]: ((k9_setfam_1 @ X62) = (k1_zfmisc_1 @ X62))),
% 0.89/1.16      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.89/1.16  thf('3', plain, (![X41 : $i]: ((k3_tarski @ (k9_setfam_1 @ X41)) = (X41))),
% 0.89/1.16      inference('demod', [status(thm)], ['1', '2'])).
% 0.89/1.16  thf(t14_yellow_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.89/1.16       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.89/1.16         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.89/1.16  thf('4', plain,
% 0.89/1.16      (![X63 : $i]:
% 0.89/1.16         (~ (r2_hidden @ (k3_tarski @ X63) @ X63)
% 0.89/1.16          | ((k4_yellow_0 @ (k2_yellow_1 @ X63)) = (k3_tarski @ X63))
% 0.89/1.16          | (v1_xboole_0 @ X63))),
% 0.89/1.16      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.89/1.16  thf('5', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.89/1.16          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.89/1.16          | ((k4_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0)))
% 0.89/1.16              = (k3_tarski @ (k9_setfam_1 @ X0))))),
% 0.89/1.16      inference('sup-', [status(thm)], ['3', '4'])).
% 0.89/1.16  thf(t4_yellow_1, axiom,
% 0.89/1.16    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.89/1.16  thf('6', plain,
% 0.89/1.16      (![X64 : $i]: ((k3_yellow_1 @ X64) = (k2_yellow_1 @ (k9_setfam_1 @ X64)))),
% 0.89/1.16      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.89/1.16  thf('7', plain, (![X41 : $i]: ((k3_tarski @ (k9_setfam_1 @ X41)) = (X41))),
% 0.89/1.16      inference('demod', [status(thm)], ['1', '2'])).
% 0.89/1.16  thf('8', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X0 @ (k9_setfam_1 @ X0))
% 0.89/1.16          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.89/1.16          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.89/1.16  thf(d10_xboole_0, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.16  thf('9', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.89/1.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.16  thf('10', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.16      inference('simplify', [status(thm)], ['9'])).
% 0.89/1.16  thf(d1_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.89/1.16       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.89/1.16  thf('11', plain,
% 0.89/1.16      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.16         (~ (r1_tarski @ X28 @ X29)
% 0.89/1.16          | (r2_hidden @ X28 @ X30)
% 0.89/1.16          | ((X30) != (k1_zfmisc_1 @ X29)))),
% 0.89/1.16      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.89/1.16  thf('12', plain,
% 0.89/1.16      (![X28 : $i, X29 : $i]:
% 0.89/1.16         ((r2_hidden @ X28 @ (k1_zfmisc_1 @ X29)) | ~ (r1_tarski @ X28 @ X29))),
% 0.89/1.16      inference('simplify', [status(thm)], ['11'])).
% 0.89/1.16  thf('13', plain, (![X62 : $i]: ((k9_setfam_1 @ X62) = (k1_zfmisc_1 @ X62))),
% 0.89/1.16      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.89/1.16  thf('14', plain,
% 0.89/1.16      (![X28 : $i, X29 : $i]:
% 0.89/1.16         ((r2_hidden @ X28 @ (k9_setfam_1 @ X29)) | ~ (r1_tarski @ X28 @ X29))),
% 0.89/1.16      inference('demod', [status(thm)], ['12', '13'])).
% 0.89/1.16  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['10', '14'])).
% 0.89/1.16  thf('16', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.89/1.16          | ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['8', '15'])).
% 0.89/1.16  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['10', '14'])).
% 0.89/1.16  thf(t6_boole, axiom,
% 0.89/1.16    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.89/1.16  thf('18', plain,
% 0.89/1.16      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.89/1.16      inference('cnf', [status(esa)], [t6_boole])).
% 0.89/1.16  thf(t60_relat_1, axiom,
% 0.89/1.16    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.89/1.16     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.89/1.16  thf('19', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.16      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.89/1.16  thf(t205_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ B ) =>
% 0.89/1.16       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.89/1.16         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.89/1.16  thf('20', plain,
% 0.89/1.16      (![X45 : $i, X46 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X46 @ (k1_relat_1 @ X45))
% 0.89/1.16          | ((k11_relat_1 @ X45 @ X46) != (k1_xboole_0))
% 0.89/1.16          | ~ (v1_relat_1 @ X45))),
% 0.89/1.16      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.89/1.16  thf('21', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.89/1.16          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.89/1.16          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.16  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ?[B:$i]:
% 0.89/1.16       ( ( ![C:$i]:
% 0.89/1.16           ( ( r2_hidden @ C @ A ) =>
% 0.89/1.16             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.89/1.16         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.89/1.16         ( v1_relat_1 @ B ) ) ))).
% 0.89/1.16  thf('22', plain, (![X48 : $i]: ((k1_relat_1 @ (sk_B_1 @ X48)) = (X48))),
% 0.89/1.16      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.89/1.16  thf(t64_relat_1, axiom,
% 0.89/1.16    (![A:$i]:
% 0.89/1.16     ( ( v1_relat_1 @ A ) =>
% 0.89/1.16       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.89/1.16           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.16         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.16  thf('23', plain,
% 0.89/1.16      (![X47 : $i]:
% 0.89/1.16         (((k1_relat_1 @ X47) != (k1_xboole_0))
% 0.89/1.16          | ((X47) = (k1_xboole_0))
% 0.89/1.16          | ~ (v1_relat_1 @ X47))),
% 0.89/1.16      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.89/1.16  thf('24', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (((X0) != (k1_xboole_0))
% 0.89/1.16          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.89/1.16          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.89/1.16      inference('sup-', [status(thm)], ['22', '23'])).
% 0.89/1.16  thf('25', plain, (![X48 : $i]: (v1_relat_1 @ (sk_B_1 @ X48))),
% 0.89/1.16      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.89/1.16  thf('26', plain,
% 0.89/1.16      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['24', '25'])).
% 0.89/1.16  thf('27', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.16      inference('simplify', [status(thm)], ['26'])).
% 0.89/1.16  thf('28', plain, (![X48 : $i]: (v1_relat_1 @ (sk_B_1 @ X48))),
% 0.89/1.16      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.89/1.16  thf('29', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.89/1.16      inference('sup+', [status(thm)], ['27', '28'])).
% 0.89/1.16  thf('30', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.89/1.16          | ((k11_relat_1 @ k1_xboole_0 @ X0) != (k1_xboole_0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['21', '29'])).
% 0.89/1.16  thf(t113_zfmisc_1, axiom,
% 0.89/1.16    (![A:$i,B:$i]:
% 0.89/1.16     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.89/1.16       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.16  thf('31', plain,
% 0.89/1.16      (![X39 : $i, X40 : $i]:
% 0.89/1.16         (((k2_zfmisc_1 @ X39 @ X40) = (k1_xboole_0))
% 0.89/1.16          | ((X40) != (k1_xboole_0)))),
% 0.89/1.16      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.89/1.16  thf('32', plain,
% 0.89/1.16      (![X39 : $i]: ((k2_zfmisc_1 @ X39 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.16      inference('simplify', [status(thm)], ['31'])).
% 0.89/1.16  thf('33', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k9_setfam_1 @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['10', '14'])).
% 0.89/1.16  thf(t203_relat_1, axiom,
% 0.89/1.16    (![A:$i,B:$i,C:$i]:
% 0.89/1.16     ( ( r2_hidden @ A @ B ) =>
% 0.89/1.16       ( ( k11_relat_1 @ ( k2_zfmisc_1 @ B @ C ) @ A ) = ( C ) ) ))).
% 0.89/1.16  thf('34', plain,
% 0.89/1.16      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X42 @ X43)
% 0.89/1.16          | ((k11_relat_1 @ (k2_zfmisc_1 @ X43 @ X44) @ X42) = (X44)))),
% 0.89/1.16      inference('cnf', [status(esa)], [t203_relat_1])).
% 0.89/1.16  thf('35', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]:
% 0.89/1.16         ((k11_relat_1 @ (k2_zfmisc_1 @ (k9_setfam_1 @ X0) @ X1) @ X0) = (X1))),
% 0.89/1.16      inference('sup-', [status(thm)], ['33', '34'])).
% 0.89/1.16  thf('36', plain,
% 0.89/1.16      (![X0 : $i]: ((k11_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.89/1.16      inference('sup+', [status(thm)], ['32', '35'])).
% 0.89/1.16  thf('37', plain,
% 0.89/1.16      (![X0 : $i]:
% 0.89/1.16         (~ (r2_hidden @ X0 @ k1_xboole_0) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.89/1.16      inference('demod', [status(thm)], ['30', '36'])).
% 0.89/1.16  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.89/1.16      inference('simplify', [status(thm)], ['37'])).
% 0.89/1.16  thf('39', plain,
% 0.89/1.16      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['18', '38'])).
% 0.89/1.16  thf('40', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.89/1.16      inference('sup-', [status(thm)], ['17', '39'])).
% 0.89/1.16  thf('41', plain, (![X0 : $i]: ((k4_yellow_0 @ (k3_yellow_1 @ X0)) = (X0))),
% 0.89/1.16      inference('clc', [status(thm)], ['16', '40'])).
% 0.89/1.16  thf('42', plain, (((sk_A) != (sk_A))),
% 0.89/1.16      inference('demod', [status(thm)], ['0', '41'])).
% 0.89/1.16  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.89/1.16  
% 0.89/1.16  % SZS output end Refutation
% 0.89/1.16  
% 0.99/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

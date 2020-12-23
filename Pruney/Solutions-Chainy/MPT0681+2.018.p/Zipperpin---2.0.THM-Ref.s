%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvvXdGp8xZ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:04 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   68 (  98 expanded)
%              Number of leaves         :   23 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  552 ( 936 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t125_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_xboole_0 @ A @ B )
          & ( v2_funct_1 @ C ) )
       => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_xboole_0 @ A @ B )
            & ( v2_funct_1 @ C ) )
         => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X44 ) @ X45 )
      | ( ( k9_relat_1 @ X44 @ X45 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_funct_1 @ X46 )
      | ( ( k9_relat_1 @ X46 @ ( k3_xboole_0 @ X47 @ X48 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X46 @ X47 ) @ ( k9_relat_1 @ X46 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('13',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( v2_funct_1 @ X46 )
      | ( ( k9_relat_1 @ X46 @ ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X46 @ X47 ) @ ( k9_relat_1 @ X46 @ X48 ) ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('17',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) @ X3 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ X3 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X0 ) ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X10: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X10 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X7 ) ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_2 @ sk_A ) @ ( k9_relat_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v2_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v2_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvvXdGp8xZ
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:40:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 551 iterations in 0.345s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.82  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.59/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.82  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.59/0.82  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.82  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.59/0.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.82  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(t125_funct_1, conjecture,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.82       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.59/0.82         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.82        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.82          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.59/0.82            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.59/0.82  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t3_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.82            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.82       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.82            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.82  thf('1', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.59/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.82  thf(t4_xboole_0, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.82            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.82       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.82            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.59/0.82  thf('2', plain,
% 0.59/0.82      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.59/0.82          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.59/0.82      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.59/0.82  thf(t12_setfam_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.82  thf('3', plain,
% 0.59/0.82      (![X42 : $i, X43 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.59/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.82  thf('4', plain,
% 0.59/0.82      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 0.59/0.82          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.59/0.82      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.59/0.82          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['1', '4'])).
% 0.59/0.82  thf('6', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (r1_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['0', '5'])).
% 0.59/0.82  thf(t151_relat_1, axiom,
% 0.59/0.82    (![A:$i,B:$i]:
% 0.59/0.82     ( ( v1_relat_1 @ B ) =>
% 0.59/0.82       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.82         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.82  thf('7', plain,
% 0.59/0.82      (![X44 : $i, X45 : $i]:
% 0.59/0.82         (~ (r1_xboole_0 @ (k1_relat_1 @ X44) @ X45)
% 0.59/0.82          | ((k9_relat_1 @ X44 @ X45) = (k1_xboole_0))
% 0.59/0.82          | ~ (v1_relat_1 @ X44))),
% 0.59/0.82      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.59/0.82  thf('8', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | ((k9_relat_1 @ X0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)))
% 0.59/0.82              = (k1_xboole_0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.82  thf('9', plain,
% 0.59/0.82      (![X4 : $i, X5 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X4 @ X5)
% 0.59/0.82          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 0.59/0.82      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.59/0.82  thf('10', plain,
% 0.59/0.82      (![X42 : $i, X43 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.59/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.82  thf('11', plain,
% 0.59/0.82      (![X4 : $i, X5 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X4 @ X5)
% 0.59/0.82          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ 
% 0.59/0.82             (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.59/0.82      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.82  thf(t121_funct_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i]:
% 0.59/0.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.59/0.82       ( ( v2_funct_1 @ C ) =>
% 0.59/0.82         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.59/0.82           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X46)
% 0.59/0.82          | ((k9_relat_1 @ X46 @ (k3_xboole_0 @ X47 @ X48))
% 0.59/0.82              = (k3_xboole_0 @ (k9_relat_1 @ X46 @ X47) @ 
% 0.59/0.82                 (k9_relat_1 @ X46 @ X48)))
% 0.59/0.82          | ~ (v1_funct_1 @ X46)
% 0.59/0.82          | ~ (v1_relat_1 @ X46))),
% 0.59/0.82      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.59/0.82  thf('13', plain,
% 0.59/0.82      (![X42 : $i, X43 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.59/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.82  thf('14', plain,
% 0.59/0.82      (![X42 : $i, X43 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.59/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.82  thf('15', plain,
% 0.59/0.82      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.59/0.82         (~ (v2_funct_1 @ X46)
% 0.59/0.82          | ((k9_relat_1 @ X46 @ (k1_setfam_1 @ (k2_tarski @ X47 @ X48)))
% 0.59/0.82              = (k1_setfam_1 @ 
% 0.59/0.82                 (k2_tarski @ (k9_relat_1 @ X46 @ X47) @ 
% 0.59/0.82                  (k9_relat_1 @ X46 @ X48))))
% 0.59/0.82          | ~ (v1_funct_1 @ X46)
% 0.59/0.82          | ~ (v1_relat_1 @ X46))),
% 0.59/0.82      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (![X4 : $i, X5 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X4 @ X5)
% 0.59/0.82          | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ 
% 0.59/0.82             (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 0.59/0.82      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.82  thf('17', plain,
% 0.59/0.82      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X2 @ X0)
% 0.59/0.82          | ~ (r2_hidden @ X2 @ X3)
% 0.59/0.82          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.59/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.82  thf('18', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X1 @ X0)
% 0.59/0.82          | ~ (r1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 0.59/0.82          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.59/0.82      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.82  thf('19', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.82         (~ (r1_xboole_0 @ 
% 0.59/0.82             (k9_relat_1 @ X2 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))) @ X3)
% 0.59/0.82          | ~ (v1_relat_1 @ X2)
% 0.59/0.82          | ~ (v1_funct_1 @ X2)
% 0.59/0.82          | ~ (v2_funct_1 @ X2)
% 0.59/0.82          | ~ (r2_hidden @ 
% 0.59/0.82               (sk_C_1 @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ X3)
% 0.59/0.82          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.59/0.82      inference('sup-', [status(thm)], ['15', '18'])).
% 0.59/0.82  thf('20', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))
% 0.59/0.82          | (r1_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))
% 0.59/0.82          | ~ (v2_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v1_relat_1 @ X1)
% 0.59/0.82          | ~ (r1_xboole_0 @ 
% 0.59/0.82               (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 0.59/0.82               (k1_setfam_1 @ 
% 0.59/0.82                (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['11', '19'])).
% 0.59/0.82  thf('21', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         (~ (r1_xboole_0 @ 
% 0.59/0.82             (k9_relat_1 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X0))) @ 
% 0.59/0.82             (k1_setfam_1 @ 
% 0.59/0.82              (k2_tarski @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0))))
% 0.59/0.82          | ~ (v1_relat_1 @ X1)
% 0.59/0.82          | ~ (v1_funct_1 @ X1)
% 0.59/0.82          | ~ (v2_funct_1 @ X1)
% 0.59/0.82          | (r1_xboole_0 @ (k9_relat_1 @ X1 @ X2) @ (k9_relat_1 @ X1 @ X0)))),
% 0.59/0.82      inference('simplify', [status(thm)], ['20'])).
% 0.59/0.82  thf('22', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (r1_xboole_0 @ k1_xboole_0 @ 
% 0.59/0.82             (k1_setfam_1 @ 
% 0.59/0.82              (k2_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))))
% 0.59/0.82          | ~ (v1_relat_1 @ X0)
% 0.59/0.82          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['8', '21'])).
% 0.59/0.82  thf('23', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('24', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.82  thf('25', plain,
% 0.59/0.82      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 0.59/0.82          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.59/0.82      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.82  thf('26', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X2)
% 0.59/0.82          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.82  thf('27', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (r1_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B)) @ X0)),
% 0.59/0.82      inference('sup-', [status(thm)], ['23', '26'])).
% 0.59/0.82  thf('28', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.59/0.82      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.82  thf(t2_boole, axiom,
% 0.59/0.82    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.82  thf('29', plain,
% 0.59/0.82      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.82      inference('cnf', [status(esa)], [t2_boole])).
% 0.59/0.82  thf('30', plain,
% 0.59/0.82      (![X42 : $i, X43 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 0.59/0.82      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.82  thf('31', plain,
% 0.59/0.82      (![X10 : $i]:
% 0.59/0.82         ((k1_setfam_1 @ (k2_tarski @ X10 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.59/0.82      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.82  thf('32', plain,
% 0.59/0.82      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X6 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X7)))
% 0.59/0.82          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.59/0.82      inference('demod', [status(thm)], ['2', '3'])).
% 0.59/0.82  thf('33', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.82  thf('34', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.59/0.82      inference('sup-', [status(thm)], ['28', '33'])).
% 0.59/0.82  thf('35', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.59/0.82      inference('sup-', [status(thm)], ['27', '34'])).
% 0.59/0.82  thf('36', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_relat_1 @ X0)
% 0.59/0.82          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('demod', [status(thm)], ['22', '35'])).
% 0.59/0.82  thf('37', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (v1_funct_1 @ X0)
% 0.59/0.82          | ~ (v2_funct_1 @ X0)
% 0.59/0.82          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.59/0.82          | ~ (v1_relat_1 @ X0))),
% 0.59/0.82      inference('simplify', [status(thm)], ['36'])).
% 0.59/0.82  thf('38', plain,
% 0.59/0.82      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_2 @ sk_A) @ 
% 0.59/0.82          (k9_relat_1 @ sk_C_2 @ sk_B))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('39', plain,
% 0.59/0.82      ((~ (v1_relat_1 @ sk_C_2)
% 0.59/0.82        | ~ (v2_funct_1 @ sk_C_2)
% 0.59/0.82        | ~ (v1_funct_1 @ sk_C_2))),
% 0.59/0.82      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.82  thf('40', plain, ((v1_relat_1 @ sk_C_2)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('41', plain, ((v2_funct_1 @ sk_C_2)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('42', plain, ((v1_funct_1 @ sk_C_2)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('43', plain, ($false),
% 0.59/0.82      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.59/0.82  
% 0.59/0.82  % SZS output end Refutation
% 0.59/0.82  
% 0.67/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ktQOLtWy6t

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:56 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 148 expanded)
%              Number of leaves         :   25 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  561 (1962 expanded)
%              Number of equality atoms :   14 (  60 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(t5_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( ( k1_relat_1 @ C )
              = A )
            & ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_3 )
    | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X18 @ X16 ) @ X18 ) @ X16 )
      | ( X17
       != ( k2_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('4',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X18 @ X16 ) @ X18 ) @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X25 @ X27 ) @ X26 )
      | ( X27
        = ( k1_funct_1 @ X26 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 )
      | ( r2_hidden @ X7 @ X10 )
      | ( X10
       != ( k1_relat_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) @ sk_C_3 ) @ sk_A )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X33: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X33 ) @ sk_B )
      | ~ ( r2_hidden @ X33 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_D_3 @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) @ sk_C_3 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) @ sk_B )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_3 ) ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B ),
    inference(simplify,[status(thm)],['22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X30 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_3 ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( $false
   <= ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ sk_C_3 )
   <= ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_3 ) @ sk_B ),
    inference(simplify,[status(thm)],['22'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X31 ) @ X32 )
      | ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ X32 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ~ ( v1_funct_1 @ sk_C_3 )
    | ( v1_funct_2 @ sk_C_3 @ ( k1_relat_1 @ sk_C_3 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_3 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,(
    ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['35','44','45'])).

thf('47',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['32','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ktQOLtWy6t
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 578 iterations in 0.415s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.68/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.68/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.88  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.68/0.88  thf(t5_funct_2, conjecture,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.68/0.88       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.68/0.88           ( ![D:$i]:
% 0.68/0.88             ( ( r2_hidden @ D @ A ) =>
% 0.68/0.88               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 0.68/0.88         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.88           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.88        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.68/0.88          ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.68/0.88              ( ![D:$i]:
% 0.68/0.88                ( ( r2_hidden @ D @ A ) =>
% 0.68/0.88                  ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 0.68/0.88            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.68/0.88              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t5_funct_2])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      ((~ (v1_funct_1 @ sk_C_3)
% 0.68/0.88        | ~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)
% 0.68/0.88        | ~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      ((~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ sk_C_3 @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.68/0.88      inference('split', [status(esa)], ['0'])).
% 0.68/0.88  thf(d3_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf(d5_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.68/0.88       ( ![C:$i]:
% 0.68/0.88         ( ( r2_hidden @ C @ B ) <=>
% 0.68/0.88           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X18 @ X17)
% 0.68/0.88          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X18 @ X16) @ X18) @ X16)
% 0.68/0.88          | ((X17) != (k2_relat_1 @ X16)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      (![X16 : $i, X18 : $i]:
% 0.68/0.88         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X18 @ X16) @ X18) @ X16)
% 0.68/0.88          | ~ (r2_hidden @ X18 @ (k2_relat_1 @ X16)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['3'])).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | (r2_hidden @ 
% 0.68/0.88             (k4_tarski @ (sk_D_3 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.68/0.88              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 0.68/0.88             X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['2', '4'])).
% 0.68/0.88  thf(t8_funct_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.68/0.88       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.68/0.88         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.68/0.88           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.68/0.88         (~ (r2_hidden @ (k4_tarski @ X25 @ X27) @ X26)
% 0.68/0.88          | ((X27) = (k1_funct_1 @ X26 @ X25))
% 0.68/0.88          | ~ (v1_funct_1 @ X26)
% 0.68/0.88          | ~ (v1_relat_1 @ X26))),
% 0.68/0.88      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | ~ (v1_relat_1 @ X0)
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.68/0.88              = (k1_funct_1 @ X0 @ 
% 0.68/0.88                 (sk_D_3 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.88  thf('8', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | (r2_hidden @ 
% 0.68/0.88             (k4_tarski @ (sk_D_3 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.68/0.88              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 0.68/0.88             X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['2', '4'])).
% 0.68/0.88  thf(d4_relat_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.68/0.88       ( ![C:$i]:
% 0.68/0.88         ( ( r2_hidden @ C @ B ) <=>
% 0.68/0.88           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.68/0.88         (~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9)
% 0.68/0.88          | (r2_hidden @ X7 @ X10)
% 0.68/0.88          | ((X10) != (k1_relat_1 @ X9)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.68/0.88         ((r2_hidden @ X7 @ (k1_relat_1 @ X9))
% 0.68/0.88          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X9))),
% 0.68/0.88      inference('simplify', [status(thm)], ['10'])).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | (r2_hidden @ (sk_D_3 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.68/0.88             (k1_relat_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['9', '11'])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ 
% 0.68/0.88           (sk_D_3 @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_3)) @ sk_C_3) @ sk_A)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['8', '12'])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X33 : $i]:
% 0.68/0.88         ((r2_hidden @ (k1_funct_1 @ sk_C_3 @ X33) @ sk_B)
% 0.68/0.88          | ~ (r2_hidden @ X33 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0)
% 0.68/0.88          | (r2_hidden @ 
% 0.68/0.88             (k1_funct_1 @ sk_C_3 @ 
% 0.68/0.88              (sk_D_3 @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_3)) @ sk_C_3)) @ 
% 0.68/0.88             sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['13', '14'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_3)) @ sk_B)
% 0.68/0.88          | ~ (v1_funct_1 @ sk_C_3)
% 0.68/0.88          | ~ (v1_relat_1 @ sk_C_3)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['7', '15'])).
% 0.68/0.88  thf('17', plain, ((v1_funct_1 @ sk_C_3)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('18', plain, ((v1_relat_1 @ sk_C_3)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_3)) @ sk_B)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0))),
% 0.68/0.88      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ X0)
% 0.68/0.88          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_3)) @ sk_B))),
% 0.68/0.88      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B)
% 0.68/0.88        | (r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('23', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B)),
% 0.68/0.88      inference('simplify', [status(thm)], ['22'])).
% 0.68/0.88  thf(d10_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('25', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.68/0.88      inference('simplify', [status(thm)], ['24'])).
% 0.68/0.88  thf(t11_relset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( v1_relat_1 @ C ) =>
% 0.68/0.88       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.68/0.88           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.68/0.88         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.68/0.88          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ X30)
% 0.68/0.88          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.68/0.88          | ~ (v1_relat_1 @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X0)
% 0.68/0.88          | (m1_subset_1 @ X0 @ 
% 0.68/0.88             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.68/0.88          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (((m1_subset_1 @ sk_C_3 @ 
% 0.68/0.88         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_3) @ sk_B)))
% 0.68/0.88        | ~ (v1_relat_1 @ sk_C_3))),
% 0.68/0.88      inference('sup-', [status(thm)], ['23', '27'])).
% 0.68/0.88  thf('29', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('30', plain, ((v1_relat_1 @ sk_C_3)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.68/0.88      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (($false)
% 0.68/0.88         <= (~
% 0.68/0.88             ((m1_subset_1 @ sk_C_3 @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '31'])).
% 0.68/0.88  thf('33', plain, ((v1_funct_1 @ sk_C_3)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('34', plain, ((~ (v1_funct_1 @ sk_C_3)) <= (~ ((v1_funct_1 @ sk_C_3)))),
% 0.68/0.88      inference('split', [status(esa)], ['0'])).
% 0.68/0.88  thf('35', plain, (((v1_funct_1 @ sk_C_3))),
% 0.68/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.68/0.88  thf('36', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_3) @ sk_B)),
% 0.68/0.88      inference('simplify', [status(thm)], ['22'])).
% 0.68/0.88  thf(t4_funct_2, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.68/0.88       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.68/0.88         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.68/0.88           ( m1_subset_1 @
% 0.68/0.88             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X31 : $i, X32 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k2_relat_1 @ X31) @ X32)
% 0.68/0.88          | (v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ X32)
% 0.68/0.88          | ~ (v1_funct_1 @ X31)
% 0.68/0.88          | ~ (v1_relat_1 @ X31))),
% 0.68/0.88      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      ((~ (v1_relat_1 @ sk_C_3)
% 0.68/0.88        | ~ (v1_funct_1 @ sk_C_3)
% 0.68/0.88        | (v1_funct_2 @ sk_C_3 @ (k1_relat_1 @ sk_C_3) @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.88  thf('39', plain, ((v1_relat_1 @ sk_C_3)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('40', plain, ((v1_funct_1 @ sk_C_3)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('41', plain, (((k1_relat_1 @ sk_C_3) = (sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('42', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)),
% 0.68/0.88      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      ((~ (v1_funct_2 @ sk_C_3 @ sk_A @ sk_B))
% 0.68/0.88         <= (~ ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)))),
% 0.68/0.88      inference('split', [status(esa)], ['0'])).
% 0.68/0.88  thf('44', plain, (((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B))),
% 0.68/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (~ ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.68/0.88       ~ ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)) | ~ ((v1_funct_1 @ sk_C_3))),
% 0.68/0.88      inference('split', [status(esa)], ['0'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (~ ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.68/0.88      inference('sat_resolution*', [status(thm)], ['35', '44', '45'])).
% 0.68/0.88  thf('47', plain, ($false),
% 0.68/0.88      inference('simpl_trail', [status(thm)], ['32', '46'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

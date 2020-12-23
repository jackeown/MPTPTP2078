%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.396wWnrsTk

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:16 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 547 expanded)
%              Number of leaves         :   32 ( 173 expanded)
%              Depth                    :   21
%              Number of atoms          : 1120 (6108 expanded)
%              Number of equality atoms :   97 ( 457 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t155_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t155_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 @ X26 @ X29 @ X31 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ( X27 != X28 )
      | ~ ( v1_partfun1 @ X27 @ X31 )
      | ~ ( r1_partfun1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,(
    ! [X26: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( r1_partfun1 @ X26 @ X28 )
      | ~ ( v1_partfun1 @ X28 @ X31 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( zip_tseitin_0 @ X28 @ X28 @ X26 @ X29 @ X31 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i,X37: $i,X39: $i,X40: $i] :
      ( ( X37
       != ( k5_partfun1 @ X35 @ X34 @ X33 ) )
      | ( r2_hidden @ X39 @ X37 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( zip_tseitin_0 @ X40 @ X39 @ X33 @ X34 @ X35 )
      | ( r2_hidden @ X39 @ ( k5_partfun1 @ X35 @ X34 @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('32',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('52',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_C_1 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('61',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','61'])).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('79',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('80',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('83',plain,
    ( ( r1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( r1_partfun1 @ X0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('86',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X26: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( r1_partfun1 @ X26 @ X28 )
      | ~ ( v1_partfun1 @ X28 @ X31 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ( zip_tseitin_0 @ X28 @ X28 @ X26 @ X29 @ X31 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_partfun1 @ k1_xboole_0 @ sk_A )
        | ~ ( r1_partfun1 @ X0 @ sk_C_1 )
        | ( zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('94',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('95',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X22 ) ) )
      | ( v1_partfun1 @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('96',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_partfun1 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('101',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('102',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ X0 @ k1_xboole_0 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','99','100','101','102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','104'])).

thf('106',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_B @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('108',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('113',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('114',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('115',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109','110','111','112','113','114'])).

thf('116',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['76','115'])).

thf('117',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('118',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['44','118'])).

thf('120',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['22','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['0','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.396wWnrsTk
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:55 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.95  % Solved by: fo/fo7.sh
% 0.76/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.95  % done 574 iterations in 0.482s
% 0.76/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.95  % SZS output start Refutation
% 0.76/0.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.76/0.95  thf(sk_D_type, type, sk_D: $i).
% 0.76/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.95  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.76/0.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.95  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.76/0.95  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.76/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.76/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.95  thf(t155_funct_2, conjecture,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95       ( ![D:$i]:
% 0.76/0.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95           ( ( r1_partfun1 @ C @ D ) =>
% 0.76/0.95             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/0.95               ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.95    (~( ![A:$i,B:$i,C:$i]:
% 0.76/0.95        ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95          ( ![D:$i]:
% 0.76/0.95            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.95                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95              ( ( r1_partfun1 @ C @ D ) =>
% 0.76/0.95                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.76/0.95                  ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) ) ) ) ) ) ) )),
% 0.76/0.95    inference('cnf.neg', [status(esa)], [t155_funct_2])).
% 0.76/0.95  thf('0', plain,
% 0.76/0.95      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('1', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('2', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(cc5_funct_2, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.95       ( ![C:$i]:
% 0.76/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.76/0.95             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.76/0.95  thf('3', plain,
% 0.76/0.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.76/0.95          | (v1_partfun1 @ X23 @ X24)
% 0.76/0.95          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.76/0.95          | ~ (v1_funct_1 @ X23)
% 0.76/0.95          | (v1_xboole_0 @ X25))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.76/0.95  thf('4', plain,
% 0.76/0.95      (((v1_xboole_0 @ sk_B)
% 0.76/0.95        | ~ (v1_funct_1 @ sk_D)
% 0.76/0.95        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B)
% 0.76/0.95        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.95  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('7', plain, (((v1_xboole_0 @ sk_B) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.76/0.95  thf('8', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(d7_partfun1, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.95         ( v1_funct_1 @ C ) ) =>
% 0.76/0.95       ( ![D:$i]:
% 0.76/0.95         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.76/0.95           ( ![E:$i]:
% 0.76/0.95             ( ( r2_hidden @ E @ D ) <=>
% 0.76/0.95               ( ?[F:$i]:
% 0.76/0.95                 ( ( v1_funct_1 @ F ) & 
% 0.76/0.95                   ( m1_subset_1 @
% 0.76/0.95                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.95                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.76/0.95                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.76/0.95  thf(zf_stmt_1, axiom,
% 0.76/0.95    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.76/0.95     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.76/0.95       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.76/0.95         ( ( F ) = ( E ) ) & 
% 0.76/0.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.76/0.95         ( v1_funct_1 @ F ) ) ))).
% 0.76/0.95  thf('9', plain,
% 0.76/0.95      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ X27 @ X28 @ X26 @ X29 @ X31)
% 0.76/0.95          | ~ (v1_funct_1 @ X27)
% 0.76/0.95          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.76/0.95          | ((X27) != (X28))
% 0.76/0.95          | ~ (v1_partfun1 @ X27 @ X31)
% 0.76/0.95          | ~ (r1_partfun1 @ X26 @ X27))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.95  thf('10', plain,
% 0.76/0.95      (![X26 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.76/0.95         (~ (r1_partfun1 @ X26 @ X28)
% 0.76/0.95          | ~ (v1_partfun1 @ X28 @ X31)
% 0.76/0.95          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.76/0.95          | ~ (v1_funct_1 @ X28)
% 0.76/0.95          | (zip_tseitin_0 @ X28 @ X28 @ X26 @ X29 @ X31))),
% 0.76/0.95      inference('simplify', [status(thm)], ['9'])).
% 0.76/0.95  thf('11', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_D)
% 0.76/0.95          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.76/0.95          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.76/0.95      inference('sup-', [status(thm)], ['8', '10'])).
% 0.76/0.95  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('13', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A)
% 0.76/0.95          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.76/0.95          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 0.76/0.95      inference('demod', [status(thm)], ['11', '12'])).
% 0.76/0.95  thf('14', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((v1_xboole_0 @ sk_B)
% 0.76/0.95          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.76/0.95          | (zip_tseitin_0 @ sk_D @ sk_D @ X0 @ sk_B @ sk_A))),
% 0.76/0.95      inference('sup-', [status(thm)], ['7', '13'])).
% 0.76/0.95  thf('15', plain,
% 0.76/0.95      (((zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ sk_B @ sk_A)
% 0.76/0.95        | (v1_xboole_0 @ sk_B))),
% 0.76/0.95      inference('sup-', [status(thm)], ['1', '14'])).
% 0.76/0.95  thf('16', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.76/0.95  thf(zf_stmt_3, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.95       ( ![D:$i]:
% 0.76/0.95         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.76/0.95           ( ![E:$i]:
% 0.76/0.95             ( ( r2_hidden @ E @ D ) <=>
% 0.76/0.95               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.76/0.95  thf('17', plain,
% 0.76/0.95      (![X33 : $i, X34 : $i, X35 : $i, X37 : $i, X39 : $i, X40 : $i]:
% 0.76/0.95         (((X37) != (k5_partfun1 @ X35 @ X34 @ X33))
% 0.76/0.95          | (r2_hidden @ X39 @ X37)
% 0.76/0.95          | ~ (zip_tseitin_0 @ X40 @ X39 @ X33 @ X34 @ X35)
% 0.76/0.95          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.76/0.95          | ~ (v1_funct_1 @ X33))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.95  thf('18', plain,
% 0.76/0.95      (![X33 : $i, X34 : $i, X35 : $i, X39 : $i, X40 : $i]:
% 0.76/0.95         (~ (v1_funct_1 @ X33)
% 0.76/0.95          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.76/0.95          | ~ (zip_tseitin_0 @ X40 @ X39 @ X33 @ X34 @ X35)
% 0.76/0.95          | (r2_hidden @ X39 @ (k5_partfun1 @ X35 @ X34 @ X33)))),
% 0.76/0.95      inference('simplify', [status(thm)], ['17'])).
% 0.76/0.95  thf('19', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.76/0.95          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C_1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['16', '18'])).
% 0.76/0.95  thf('20', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('21', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.76/0.95          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('22', plain,
% 0.76/0.95      (((v1_xboole_0 @ sk_B)
% 0.76/0.95        | (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['15', '21'])).
% 0.76/0.95  thf(d3_tarski, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.95  thf('23', plain,
% 0.76/0.95      (![X1 : $i, X3 : $i]:
% 0.76/0.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.95  thf(d10_xboole_0, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.95  thf('24', plain,
% 0.76/0.95      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.76/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.95  thf('25', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.76/0.95      inference('simplify', [status(thm)], ['24'])).
% 0.76/0.95  thf(t3_subset, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.95  thf('26', plain,
% 0.76/0.95      (![X11 : $i, X13 : $i]:
% 0.76/0.95         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.76/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.95  thf('27', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.95  thf(t5_subset, axiom,
% 0.76/0.95    (![A:$i,B:$i,C:$i]:
% 0.76/0.95     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.76/0.95          ( v1_xboole_0 @ C ) ) ))).
% 0.76/0.95  thf('28', plain,
% 0.76/0.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X17 @ X18)
% 0.76/0.95          | ~ (v1_xboole_0 @ X19)
% 0.76/0.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.95  thf('29', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/0.95  thf('30', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['23', '29'])).
% 0.76/0.95  thf(t4_subset_1, axiom,
% 0.76/0.95    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.95  thf('31', plain,
% 0.76/0.95      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.76/0.95      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.95  thf('32', plain,
% 0.76/0.95      (![X11 : $i, X12 : $i]:
% 0.76/0.95         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.95  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.95      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.95  thf('34', plain,
% 0.76/0.95      (![X4 : $i, X6 : $i]:
% 0.76/0.95         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.76/0.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.95  thf('35', plain,
% 0.76/0.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.95  thf('36', plain,
% 0.76/0.95      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['30', '35'])).
% 0.76/0.95  thf('37', plain,
% 0.76/0.95      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['30', '35'])).
% 0.76/0.95  thf('38', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.76/0.95      inference('sup+', [status(thm)], ['36', '37'])).
% 0.76/0.95  thf('39', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('40', plain,
% 0.76/0.95      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('41', plain,
% 0.76/0.95      ((![X0 : $i]:
% 0.76/0.95          (((X0) != (k1_xboole_0))
% 0.76/0.95           | ~ (v1_xboole_0 @ X0)
% 0.76/0.95           | ~ (v1_xboole_0 @ sk_B)))
% 0.76/0.95         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['38', '40'])).
% 0.76/0.95  thf('42', plain,
% 0.76/0.95      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.76/0.95         <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.95      inference('simplify', [status(thm)], ['41'])).
% 0.76/0.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.95  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.95  thf('44', plain,
% 0.76/0.95      ((~ (v1_xboole_0 @ sk_B)) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.76/0.95      inference('simplify_reflect+', [status(thm)], ['42', '43'])).
% 0.76/0.95  thf('45', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('46', plain,
% 0.76/0.95      (~ (r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('47', plain,
% 0.76/0.95      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C_1)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.95  thf('48', plain,
% 0.76/0.95      (![X1 : $i, X3 : $i]:
% 0.76/0.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.95  thf('49', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('50', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('51', plain,
% 0.76/0.95      (((m1_subset_1 @ sk_C_1 @ 
% 0.76/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['49', '50'])).
% 0.76/0.95  thf(t113_zfmisc_1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.95       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.95  thf('52', plain,
% 0.76/0.95      (![X8 : $i, X9 : $i]:
% 0.76/0.95         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.76/0.95  thf('53', plain,
% 0.76/0.95      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['52'])).
% 0.76/0.95  thf('54', plain,
% 0.76/0.95      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['51', '53'])).
% 0.76/0.95  thf('55', plain,
% 0.76/0.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X17 @ X18)
% 0.76/0.95          | ~ (v1_xboole_0 @ X19)
% 0.76/0.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.95  thf('56', plain,
% 0.76/0.95      ((![X0 : $i]:
% 0.76/0.95          (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['54', '55'])).
% 0.76/0.95  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.95  thf('58', plain,
% 0.76/0.95      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['56', '57'])).
% 0.76/0.95  thf('59', plain,
% 0.76/0.95      ((![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['48', '58'])).
% 0.76/0.95  thf('60', plain,
% 0.76/0.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.95  thf('61', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('62', plain,
% 0.76/0.95      ((~ (r2_hidden @ sk_D @ (k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['47', '61'])).
% 0.76/0.95  thf('63', plain,
% 0.76/0.95      (![X1 : $i, X3 : $i]:
% 0.76/0.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.95      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.95  thf('64', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('65', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('66', plain,
% 0.76/0.95      (((m1_subset_1 @ sk_D @ 
% 0.76/0.95         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['64', '65'])).
% 0.76/0.95  thf('67', plain,
% 0.76/0.95      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['52'])).
% 0.76/0.95  thf('68', plain,
% 0.76/0.95      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['66', '67'])).
% 0.76/0.95  thf('69', plain,
% 0.76/0.95      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.95         (~ (r2_hidden @ X17 @ X18)
% 0.76/0.95          | ~ (v1_xboole_0 @ X19)
% 0.76/0.95          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.76/0.95      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.95  thf('70', plain,
% 0.76/0.95      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['68', '69'])).
% 0.76/0.95  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.95  thf('72', plain,
% 0.76/0.95      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['70', '71'])).
% 0.76/0.95  thf('73', plain,
% 0.76/0.95      ((![X0 : $i]: (r1_tarski @ sk_D @ X0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['63', '72'])).
% 0.76/0.95  thf('74', plain,
% 0.76/0.95      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['33', '34'])).
% 0.76/0.95  thf('75', plain,
% 0.76/0.95      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.95  thf('76', plain,
% 0.76/0.95      ((~ (r2_hidden @ k1_xboole_0 @ 
% 0.76/0.95           (k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['62', '75'])).
% 0.76/0.95  thf('77', plain,
% 0.76/0.95      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['30', '35'])).
% 0.76/0.95  thf('78', plain,
% 0.76/0.95      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.95      inference('sup-', [status(thm)], ['30', '35'])).
% 0.76/0.95  thf('79', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('80', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('81', plain,
% 0.76/0.95      (((r1_partfun1 @ k1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['79', '80'])).
% 0.76/0.95  thf('82', plain,
% 0.76/0.95      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.95  thf('83', plain,
% 0.76/0.95      (((r1_partfun1 @ k1_xboole_0 @ k1_xboole_0))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)], ['81', '82'])).
% 0.76/0.95  thf('84', plain,
% 0.76/0.95      ((![X0 : $i]: ((r1_partfun1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['78', '83'])).
% 0.76/0.95  thf('85', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('86', plain,
% 0.76/0.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('87', plain,
% 0.76/0.95      (![X26 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.76/0.95         (~ (r1_partfun1 @ X26 @ X28)
% 0.76/0.95          | ~ (v1_partfun1 @ X28 @ X31)
% 0.76/0.95          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 0.76/0.95          | ~ (v1_funct_1 @ X28)
% 0.76/0.95          | (zip_tseitin_0 @ X28 @ X28 @ X26 @ X29 @ X31))),
% 0.76/0.95      inference('simplify', [status(thm)], ['9'])).
% 0.76/0.95  thf('88', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A)
% 0.76/0.95          | ~ (v1_funct_1 @ sk_C_1)
% 0.76/0.95          | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.76/0.95          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.76/0.95      inference('sup-', [status(thm)], ['86', '87'])).
% 0.76/0.95  thf('89', plain, ((v1_funct_1 @ sk_C_1)),
% 0.76/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.95  thf('90', plain,
% 0.76/0.95      (![X0 : $i]:
% 0.76/0.95         ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A)
% 0.76/0.95          | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.76/0.95          | ~ (r1_partfun1 @ X0 @ sk_C_1))),
% 0.76/0.95      inference('demod', [status(thm)], ['88', '89'])).
% 0.76/0.95  thf('91', plain,
% 0.76/0.95      ((![X0 : $i]:
% 0.76/0.95          (~ (v1_partfun1 @ k1_xboole_0 @ sk_A)
% 0.76/0.95           | ~ (r1_partfun1 @ X0 @ sk_C_1)
% 0.76/0.95           | (zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ X0 @ sk_B @ sk_A)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['85', '90'])).
% 0.76/0.95  thf('92', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('93', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/0.95  thf('94', plain,
% 0.76/0.95      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.76/0.95      inference('simplify', [status(thm)], ['52'])).
% 0.76/0.95  thf(cc1_partfun1, axiom,
% 0.76/0.95    (![A:$i,B:$i]:
% 0.76/0.95     ( ( v1_xboole_0 @ A ) =>
% 0.76/0.95       ( ![C:$i]:
% 0.76/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.95           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.76/0.95  thf('95', plain,
% 0.76/0.95      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.95         (~ (v1_xboole_0 @ X20)
% 0.76/0.95          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X22)))
% 0.76/0.95          | (v1_partfun1 @ X21 @ X20))),
% 0.76/0.95      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.76/0.95  thf('96', plain,
% 0.76/0.95      (![X1 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.76/0.95          | (v1_partfun1 @ X1 @ k1_xboole_0)
% 0.76/0.95          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.76/0.95      inference('sup-', [status(thm)], ['94', '95'])).
% 0.76/0.95  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.95  thf('98', plain,
% 0.76/0.95      (![X1 : $i]:
% 0.76/0.95         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.76/0.95          | (v1_partfun1 @ X1 @ k1_xboole_0))),
% 0.76/0.95      inference('demod', [status(thm)], ['96', '97'])).
% 0.76/0.95  thf('99', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.95      inference('sup-', [status(thm)], ['93', '98'])).
% 0.76/0.95  thf('100', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('101', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('102', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('103', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('104', plain,
% 0.76/0.95      ((![X0 : $i]:
% 0.76/0.95          (~ (r1_partfun1 @ X0 @ k1_xboole_0)
% 0.76/0.95           | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ 
% 0.76/0.95              k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['91', '92', '99', '100', '101', '102', '103'])).
% 0.76/0.95  thf('105', plain,
% 0.76/0.95      ((![X0 : $i]:
% 0.76/0.95          (~ (v1_xboole_0 @ X0)
% 0.76/0.95           | (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X0 @ sk_B @ 
% 0.76/0.95              k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['84', '104'])).
% 0.76/0.95  thf('106', plain,
% 0.76/0.95      ((![X0 : $i, X1 : $i]:
% 0.76/0.95          ((zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 @ X1 @ sk_B @ X0)
% 0.76/0.95           | ~ (v1_xboole_0 @ X0)
% 0.76/0.95           | ~ (v1_xboole_0 @ X1)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup+', [status(thm)], ['77', '105'])).
% 0.76/0.95  thf('107', plain,
% 0.76/0.95      (![X0 : $i, X1 : $i]:
% 0.76/0.95         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))
% 0.76/0.95          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ sk_B @ sk_A))),
% 0.76/0.95      inference('demod', [status(thm)], ['19', '20'])).
% 0.76/0.95  thf('108', plain,
% 0.76/0.95      (((~ (v1_xboole_0 @ sk_C_1)
% 0.76/0.95         | ~ (v1_xboole_0 @ sk_A)
% 0.76/0.95         | (r2_hidden @ k1_xboole_0 @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['106', '107'])).
% 0.76/0.95  thf('109', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.95  thf('111', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.95  thf('113', plain,
% 0.76/0.95      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('114', plain,
% 0.76/0.95      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('sup-', [status(thm)], ['59', '60'])).
% 0.76/0.95  thf('115', plain,
% 0.76/0.95      (((r2_hidden @ k1_xboole_0 @ 
% 0.76/0.95         (k5_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.76/0.95         <= ((((sk_A) = (k1_xboole_0))))),
% 0.76/0.95      inference('demod', [status(thm)],
% 0.76/0.95                ['108', '109', '110', '111', '112', '113', '114'])).
% 0.76/0.95  thf('116', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.76/0.95      inference('demod', [status(thm)], ['76', '115'])).
% 0.76/0.95  thf('117', plain,
% 0.76/0.95      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.76/0.95      inference('split', [status(esa)], ['39'])).
% 0.76/0.95  thf('118', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.76/0.95      inference('sat_resolution*', [status(thm)], ['116', '117'])).
% 0.76/0.95  thf('119', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.76/0.95      inference('simpl_trail', [status(thm)], ['44', '118'])).
% 0.76/0.95  thf('120', plain,
% 0.76/0.95      ((r2_hidden @ sk_D @ (k5_partfun1 @ sk_A @ sk_B @ sk_C_1))),
% 0.76/0.95      inference('clc', [status(thm)], ['22', '119'])).
% 0.76/0.95  thf('121', plain, ($false), inference('demod', [status(thm)], ['0', '120'])).
% 0.76/0.95  
% 0.76/0.95  % SZS output end Refutation
% 0.76/0.95  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

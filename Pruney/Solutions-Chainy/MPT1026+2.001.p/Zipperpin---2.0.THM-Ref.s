%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A3wRb3Lb2p

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:52 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 668 expanded)
%              Number of leaves         :   51 ( 208 expanded)
%              Depth                    :   19
%              Number of atoms          : 1021 (7199 expanded)
%              Number of equality atoms :   37 ( 261 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(o_1_0_funct_1_type,type,(
    o_1_0_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X44 ) ) )
      | ( v1_partfun1 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_partfun1 @ X39 @ X40 )
      | ( v1_funct_2 @ X39 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_funct_2 @ X2 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t121_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t121_funct_2])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 ) )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    r2_hidden @ sk_C_2 @ ( k1_funct_2 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( ( v1_relat_1 @ E )
              & ( v1_funct_1 @ E )
              & ( D = E )
              & ( ( k1_relat_1 @ E )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X60: $i,X61: $i,X62: $i,X63: $i] :
      ( ~ ( r2_hidden @ X63 @ X62 )
      | ( zip_tseitin_2 @ ( sk_E_1 @ X63 @ X60 @ X61 ) @ X63 @ X60 @ X61 )
      | ( X62
       != ( k1_funct_2 @ X61 @ X60 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X60: $i,X61: $i,X63: $i] :
      ( ( zip_tseitin_2 @ ( sk_E_1 @ X63 @ X60 @ X61 ) @ X63 @ X60 @ X61 )
      | ~ ( r2_hidden @ X63 @ ( k1_funct_2 @ X61 @ X60 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    zip_tseitin_2 @ ( sk_E_1 @ sk_C_2 @ sk_B_2 @ sk_A ) @ sk_C_2 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    zip_tseitin_2 @ ( sk_E_1 @ sk_C_2 @ sk_B_2 @ sk_A ) @ sk_C_2 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['15','17'])).

thf('20',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( X55 = X53 )
      | ~ ( zip_tseitin_2 @ X53 @ X55 @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,
    ( sk_C_2
    = ( sk_E_1 @ sk_C_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( v1_funct_1 @ X53 )
      | ~ ( zip_tseitin_2 @ X53 @ X55 @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C_2 ) )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['14','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
   <= ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['12'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['18','21'])).

thf('34',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X53 ) @ X54 )
      | ~ ( zip_tseitin_2 @ X53 @ X55 @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['18','21'])).

thf('37',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( ( k1_relat_1 @ X53 )
        = X56 )
      | ~ ( zip_tseitin_2 @ X53 @ X55 @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X38 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A ),
    inference(demod,[status(thm)],['18','21'])).

thf('42',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ( v1_relat_1 @ X53 )
      | ~ ( zip_tseitin_2 @ X53 @ X55 @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ sk_A @ X0 )
      | ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_2 ) ) )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['12'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['12'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['28','48','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['25','50'])).

thf(dt_o_1_0_funct_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( o_1_0_funct_1 @ A ) @ A ) )).

thf('52',plain,(
    ! [X27: $i] :
      ( m1_subset_1 @ ( o_1_0_funct_1 @ X27 ) @ X27 ) ),
    inference(cnf,[status(esa)],[dt_o_1_0_funct_1])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( o_1_0_funct_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( r2_hidden @ ( k4_tarski @ X23 @ X26 ) @ X24 )
      | ( X26
       != ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('57',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v1_funct_1 @ X24 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( k1_funct_1 @ X24 @ X23 ) ) @ X24 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['41','42'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( k1_funct_1 @ sk_C_2 @ X0 ) ) @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( o_1_0_funct_1 @ sk_A ) @ ( k1_funct_1 @ sk_C_2 @ ( o_1_0_funct_1 @ sk_A ) ) ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['51','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('68',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('70',plain,(
    ! [X45: $i,X46: $i] :
      ( ( zip_tseitin_0 @ X45 @ X46 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('71',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf(zf_stmt_5,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( zip_tseitin_0 @ X50 @ X51 )
      | ( zip_tseitin_1 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('73',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['32','45'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('75',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('76',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('78',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2 )
    = sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( X47
       != ( k1_relset_1 @ X47 @ X48 @ X49 ) )
      | ( v1_funct_2 @ X49 @ X47 @ X48 )
      | ~ ( zip_tseitin_1 @ X49 @ X48 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('80',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A )
    | ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 )
    | ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference(split,[status(esa)],['12'])).

thf('83',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['28','48','49'])).

thf('84',plain,(
    ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['81','84'])).

thf('86',plain,(
    ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['73','85'])).

thf('87',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','86'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('88',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('89',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('92',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['69','87','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['66','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.A3wRb3Lb2p
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.97/4.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.97/4.20  % Solved by: fo/fo7.sh
% 3.97/4.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.97/4.20  % done 2154 iterations in 3.734s
% 3.97/4.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.97/4.20  % SZS output start Refutation
% 3.97/4.20  thf(sk_B_type, type, sk_B: $i > $i).
% 3.97/4.20  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.97/4.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.97/4.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.97/4.20  thf(o_1_0_funct_1_type, type, o_1_0_funct_1: $i > $i).
% 3.97/4.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.97/4.20  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 3.97/4.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.97/4.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.97/4.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.97/4.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.97/4.20  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.97/4.20  thf(sk_A_type, type, sk_A: $i).
% 3.97/4.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.97/4.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.97/4.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.97/4.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.97/4.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.97/4.20  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.97/4.20  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 3.97/4.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.97/4.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.97/4.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.97/4.20  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 3.97/4.20  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 3.97/4.20  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.97/4.20  thf(sk_B_2_type, type, sk_B_2: $i).
% 3.97/4.20  thf(d3_tarski, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( r1_tarski @ A @ B ) <=>
% 3.97/4.20       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.97/4.20  thf('0', plain,
% 3.97/4.20      (![X4 : $i, X6 : $i]:
% 3.97/4.20         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf(d1_xboole_0, axiom,
% 3.97/4.20    (![A:$i]:
% 3.97/4.20     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.97/4.20  thf('1', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.97/4.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.97/4.20  thf('2', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['0', '1'])).
% 3.97/4.20  thf(t3_subset, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.97/4.20  thf('3', plain,
% 3.97/4.20      (![X11 : $i, X13 : $i]:
% 3.97/4.20         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 3.97/4.20      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.20  thf('4', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['2', '3'])).
% 3.97/4.20  thf(cc1_partfun1, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( v1_xboole_0 @ A ) =>
% 3.97/4.20       ( ![C:$i]:
% 3.97/4.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.20           ( v1_partfun1 @ C @ A ) ) ) ))).
% 3.97/4.20  thf('5', plain,
% 3.97/4.20      (![X42 : $i, X43 : $i, X44 : $i]:
% 3.97/4.20         (~ (v1_xboole_0 @ X42)
% 3.97/4.20          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X44)))
% 3.97/4.20          | (v1_partfun1 @ X43 @ X42))),
% 3.97/4.20      inference('cnf', [status(esa)], [cc1_partfun1])).
% 3.97/4.20  thf('6', plain,
% 3.97/4.20      (![X1 : $i, X2 : $i]:
% 3.97/4.20         (~ (v1_xboole_0 @ X2) | (v1_partfun1 @ X2 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.97/4.20      inference('sup-', [status(thm)], ['4', '5'])).
% 3.97/4.20  thf('7', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['2', '3'])).
% 3.97/4.20  thf(cc1_funct_2, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.20       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 3.97/4.20         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 3.97/4.20  thf('8', plain,
% 3.97/4.20      (![X39 : $i, X40 : $i, X41 : $i]:
% 3.97/4.20         (~ (v1_funct_1 @ X39)
% 3.97/4.20          | ~ (v1_partfun1 @ X39 @ X40)
% 3.97/4.20          | (v1_funct_2 @ X39 @ X40 @ X41)
% 3.97/4.20          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 3.97/4.20      inference('cnf', [status(esa)], [cc1_funct_2])).
% 3.97/4.20  thf('9', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.20         (~ (v1_xboole_0 @ X2)
% 3.97/4.20          | (v1_funct_2 @ X2 @ X1 @ X0)
% 3.97/4.20          | ~ (v1_partfun1 @ X2 @ X1)
% 3.97/4.20          | ~ (v1_funct_1 @ X2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['7', '8'])).
% 3.97/4.20  thf('10', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.20         (~ (v1_xboole_0 @ X0)
% 3.97/4.20          | ~ (v1_xboole_0 @ X1)
% 3.97/4.20          | ~ (v1_funct_1 @ X1)
% 3.97/4.20          | (v1_funct_2 @ X1 @ X0 @ X2)
% 3.97/4.20          | ~ (v1_xboole_0 @ X1))),
% 3.97/4.20      inference('sup-', [status(thm)], ['6', '9'])).
% 3.97/4.20  thf('11', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.20         ((v1_funct_2 @ X1 @ X0 @ X2)
% 3.97/4.20          | ~ (v1_funct_1 @ X1)
% 3.97/4.20          | ~ (v1_xboole_0 @ X1)
% 3.97/4.20          | ~ (v1_xboole_0 @ X0))),
% 3.97/4.20      inference('simplify', [status(thm)], ['10'])).
% 3.97/4.20  thf(t121_funct_2, conjecture,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 3.97/4.20       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.97/4.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.97/4.20  thf(zf_stmt_0, negated_conjecture,
% 3.97/4.20    (~( ![A:$i,B:$i,C:$i]:
% 3.97/4.20        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 3.97/4.20          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.97/4.20            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 3.97/4.20    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 3.97/4.20  thf('12', plain,
% 3.97/4.20      ((~ (v1_funct_1 @ sk_C_2)
% 3.97/4.20        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)
% 3.97/4.20        | ~ (m1_subset_1 @ sk_C_2 @ 
% 3.97/4.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.20  thf('13', plain,
% 3.97/4.20      ((~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2))
% 3.97/4.20         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('split', [status(esa)], ['12'])).
% 3.97/4.20  thf('14', plain,
% 3.97/4.20      (((~ (v1_xboole_0 @ sk_A)
% 3.97/4.20         | ~ (v1_xboole_0 @ sk_C_2)
% 3.97/4.20         | ~ (v1_funct_1 @ sk_C_2)))
% 3.97/4.20         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['11', '13'])).
% 3.97/4.20  thf('15', plain, ((r2_hidden @ sk_C_2 @ (k1_funct_2 @ sk_A @ sk_B_2))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.20  thf(d2_funct_2, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 3.97/4.20       ( ![D:$i]:
% 3.97/4.20         ( ( r2_hidden @ D @ C ) <=>
% 3.97/4.20           ( ?[E:$i]:
% 3.97/4.20             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 3.97/4.20               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 3.97/4.20               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 3.97/4.20  thf(zf_stmt_1, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 3.97/4.20  thf(zf_stmt_2, axiom,
% 3.97/4.20    (![E:$i,D:$i,B:$i,A:$i]:
% 3.97/4.20     ( ( zip_tseitin_2 @ E @ D @ B @ A ) <=>
% 3.97/4.20       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 3.97/4.20         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 3.97/4.20         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 3.97/4.20  thf(zf_stmt_3, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 3.97/4.20       ( ![D:$i]:
% 3.97/4.20         ( ( r2_hidden @ D @ C ) <=>
% 3.97/4.20           ( ?[E:$i]: ( zip_tseitin_2 @ E @ D @ B @ A ) ) ) ) ))).
% 3.97/4.20  thf('16', plain,
% 3.97/4.20      (![X60 : $i, X61 : $i, X62 : $i, X63 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X63 @ X62)
% 3.97/4.20          | (zip_tseitin_2 @ (sk_E_1 @ X63 @ X60 @ X61) @ X63 @ X60 @ X61)
% 3.97/4.20          | ((X62) != (k1_funct_2 @ X61 @ X60)))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.97/4.20  thf('17', plain,
% 3.97/4.20      (![X60 : $i, X61 : $i, X63 : $i]:
% 3.97/4.20         ((zip_tseitin_2 @ (sk_E_1 @ X63 @ X60 @ X61) @ X63 @ X60 @ X61)
% 3.97/4.20          | ~ (r2_hidden @ X63 @ (k1_funct_2 @ X61 @ X60)))),
% 3.97/4.20      inference('simplify', [status(thm)], ['16'])).
% 3.97/4.20  thf('18', plain,
% 3.97/4.20      ((zip_tseitin_2 @ (sk_E_1 @ sk_C_2 @ sk_B_2 @ sk_A) @ sk_C_2 @ sk_B_2 @ 
% 3.97/4.20        sk_A)),
% 3.97/4.20      inference('sup-', [status(thm)], ['15', '17'])).
% 3.97/4.20  thf('19', plain,
% 3.97/4.20      ((zip_tseitin_2 @ (sk_E_1 @ sk_C_2 @ sk_B_2 @ sk_A) @ sk_C_2 @ sk_B_2 @ 
% 3.97/4.20        sk_A)),
% 3.97/4.20      inference('sup-', [status(thm)], ['15', '17'])).
% 3.97/4.20  thf('20', plain,
% 3.97/4.20      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.97/4.20         (((X55) = (X53)) | ~ (zip_tseitin_2 @ X53 @ X55 @ X54 @ X56))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.97/4.20  thf('21', plain, (((sk_C_2) = (sk_E_1 @ sk_C_2 @ sk_B_2 @ sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['19', '20'])).
% 3.97/4.20  thf('22', plain, ((zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A)),
% 3.97/4.20      inference('demod', [status(thm)], ['18', '21'])).
% 3.97/4.20  thf('23', plain,
% 3.97/4.20      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.97/4.20         ((v1_funct_1 @ X53) | ~ (zip_tseitin_2 @ X53 @ X55 @ X54 @ X56))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.97/4.20  thf('24', plain, ((v1_funct_1 @ sk_C_2)),
% 3.97/4.20      inference('sup-', [status(thm)], ['22', '23'])).
% 3.97/4.20  thf('25', plain,
% 3.97/4.20      (((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C_2)))
% 3.97/4.20         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('demod', [status(thm)], ['14', '24'])).
% 3.97/4.20  thf('26', plain, ((v1_funct_1 @ sk_C_2)),
% 3.97/4.20      inference('sup-', [status(thm)], ['22', '23'])).
% 3.97/4.20  thf('27', plain, ((~ (v1_funct_1 @ sk_C_2)) <= (~ ((v1_funct_1 @ sk_C_2)))),
% 3.97/4.20      inference('split', [status(esa)], ['12'])).
% 3.97/4.20  thf('28', plain, (((v1_funct_1 @ sk_C_2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['26', '27'])).
% 3.97/4.20  thf('29', plain,
% 3.97/4.20      (![X4 : $i, X6 : $i]:
% 3.97/4.20         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf('30', plain,
% 3.97/4.20      (![X4 : $i, X6 : $i]:
% 3.97/4.20         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 3.97/4.20      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.20  thf('31', plain,
% 3.97/4.20      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['29', '30'])).
% 3.97/4.20  thf('32', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.97/4.20      inference('simplify', [status(thm)], ['31'])).
% 3.97/4.20  thf('33', plain, ((zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A)),
% 3.97/4.20      inference('demod', [status(thm)], ['18', '21'])).
% 3.97/4.20  thf('34', plain,
% 3.97/4.20      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.97/4.20         ((r1_tarski @ (k2_relat_1 @ X53) @ X54)
% 3.97/4.20          | ~ (zip_tseitin_2 @ X53 @ X55 @ X54 @ X56))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.97/4.20  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_2)),
% 3.97/4.20      inference('sup-', [status(thm)], ['33', '34'])).
% 3.97/4.20  thf('36', plain, ((zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A)),
% 3.97/4.20      inference('demod', [status(thm)], ['18', '21'])).
% 3.97/4.20  thf('37', plain,
% 3.97/4.20      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.97/4.20         (((k1_relat_1 @ X53) = (X56))
% 3.97/4.20          | ~ (zip_tseitin_2 @ X53 @ X55 @ X54 @ X56))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.97/4.20  thf('38', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.20  thf(t11_relset_1, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( v1_relat_1 @ C ) =>
% 3.97/4.20       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 3.97/4.20           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 3.97/4.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.97/4.20  thf('39', plain,
% 3.97/4.20      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.97/4.20         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 3.97/4.20          | ~ (r1_tarski @ (k2_relat_1 @ X36) @ X38)
% 3.97/4.20          | (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.97/4.20          | ~ (v1_relat_1 @ X36))),
% 3.97/4.20      inference('cnf', [status(esa)], [t11_relset_1])).
% 3.97/4.20  thf('40', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         (~ (r1_tarski @ sk_A @ X0)
% 3.97/4.20          | ~ (v1_relat_1 @ sk_C_2)
% 3.97/4.20          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 3.97/4.20          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 3.97/4.20      inference('sup-', [status(thm)], ['38', '39'])).
% 3.97/4.20  thf('41', plain, ((zip_tseitin_2 @ sk_C_2 @ sk_C_2 @ sk_B_2 @ sk_A)),
% 3.97/4.20      inference('demod', [status(thm)], ['18', '21'])).
% 3.97/4.20  thf('42', plain,
% 3.97/4.20      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 3.97/4.20         ((v1_relat_1 @ X53) | ~ (zip_tseitin_2 @ X53 @ X55 @ X54 @ X56))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.97/4.20  thf('43', plain, ((v1_relat_1 @ sk_C_2)),
% 3.97/4.20      inference('sup-', [status(thm)], ['41', '42'])).
% 3.97/4.20  thf('44', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]:
% 3.97/4.20         (~ (r1_tarski @ sk_A @ X0)
% 3.97/4.20          | (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 3.97/4.20          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X1))),
% 3.97/4.20      inference('demod', [status(thm)], ['40', '43'])).
% 3.97/4.20  thf('45', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_2)))
% 3.97/4.20          | ~ (r1_tarski @ sk_A @ X0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['35', '44'])).
% 3.97/4.20  thf('46', plain,
% 3.97/4.20      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['32', '45'])).
% 3.97/4.20  thf('47', plain,
% 3.97/4.20      ((~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 3.97/4.20         <= (~
% 3.97/4.20             ((m1_subset_1 @ sk_C_2 @ 
% 3.97/4.20               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))))),
% 3.97/4.20      inference('split', [status(esa)], ['12'])).
% 3.97/4.20  thf('48', plain,
% 3.97/4.20      (((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))),
% 3.97/4.20      inference('sup-', [status(thm)], ['46', '47'])).
% 3.97/4.20  thf('49', plain,
% 3.97/4.20      (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)) | 
% 3.97/4.20       ~
% 3.97/4.20       ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))) | 
% 3.97/4.20       ~ ((v1_funct_1 @ sk_C_2))),
% 3.97/4.20      inference('split', [status(esa)], ['12'])).
% 3.97/4.20  thf('50', plain, (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2))),
% 3.97/4.20      inference('sat_resolution*', [status(thm)], ['28', '48', '49'])).
% 3.97/4.20  thf('51', plain, ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C_2))),
% 3.97/4.20      inference('simpl_trail', [status(thm)], ['25', '50'])).
% 3.97/4.20  thf(dt_o_1_0_funct_1, axiom,
% 3.97/4.20    (![A:$i]: ( m1_subset_1 @ ( o_1_0_funct_1 @ A ) @ A ))).
% 3.97/4.20  thf('52', plain, (![X27 : $i]: (m1_subset_1 @ (o_1_0_funct_1 @ X27) @ X27)),
% 3.97/4.20      inference('cnf', [status(esa)], [dt_o_1_0_funct_1])).
% 3.97/4.20  thf(d2_subset_1, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( ( v1_xboole_0 @ A ) =>
% 3.97/4.20         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.97/4.20       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.97/4.20         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.97/4.20  thf('53', plain,
% 3.97/4.20      (![X7 : $i, X8 : $i]:
% 3.97/4.20         (~ (m1_subset_1 @ X7 @ X8)
% 3.97/4.20          | (r2_hidden @ X7 @ X8)
% 3.97/4.20          | (v1_xboole_0 @ X8))),
% 3.97/4.20      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.97/4.20  thf('54', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         ((v1_xboole_0 @ X0) | (r2_hidden @ (o_1_0_funct_1 @ X0) @ X0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['52', '53'])).
% 3.97/4.20  thf('55', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.20  thf(d4_funct_1, axiom,
% 3.97/4.20    (![A:$i]:
% 3.97/4.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.97/4.20       ( ![B:$i,C:$i]:
% 3.97/4.20         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 3.97/4.20             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 3.97/4.20               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 3.97/4.20           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 3.97/4.20             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 3.97/4.20               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 3.97/4.20  thf('56', plain,
% 3.97/4.20      (![X23 : $i, X24 : $i, X26 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ X23 @ X26) @ X24)
% 3.97/4.20          | ((X26) != (k1_funct_1 @ X24 @ X23))
% 3.97/4.20          | ~ (v1_funct_1 @ X24)
% 3.97/4.20          | ~ (v1_relat_1 @ X24))),
% 3.97/4.20      inference('cnf', [status(esa)], [d4_funct_1])).
% 3.97/4.20  thf('57', plain,
% 3.97/4.20      (![X23 : $i, X24 : $i]:
% 3.97/4.20         (~ (v1_relat_1 @ X24)
% 3.97/4.20          | ~ (v1_funct_1 @ X24)
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ X23 @ (k1_funct_1 @ X24 @ X23)) @ X24)
% 3.97/4.20          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X24)))),
% 3.97/4.20      inference('simplify', [status(thm)], ['56'])).
% 3.97/4.20  thf('58', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X0 @ sk_A)
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2)
% 3.97/4.20          | ~ (v1_funct_1 @ sk_C_2)
% 3.97/4.20          | ~ (v1_relat_1 @ sk_C_2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['55', '57'])).
% 3.97/4.20  thf('59', plain, ((v1_funct_1 @ sk_C_2)),
% 3.97/4.20      inference('sup-', [status(thm)], ['22', '23'])).
% 3.97/4.20  thf('60', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X0 @ sk_A)
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2)
% 3.97/4.20          | ~ (v1_relat_1 @ sk_C_2))),
% 3.97/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.97/4.20  thf('61', plain, ((v1_relat_1 @ sk_C_2)),
% 3.97/4.20      inference('sup-', [status(thm)], ['41', '42'])).
% 3.97/4.20  thf('62', plain,
% 3.97/4.20      (![X0 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X0 @ sk_A)
% 3.97/4.20          | (r2_hidden @ (k4_tarski @ X0 @ (k1_funct_1 @ sk_C_2 @ X0)) @ sk_C_2))),
% 3.97/4.20      inference('demod', [status(thm)], ['60', '61'])).
% 3.97/4.20  thf('63', plain,
% 3.97/4.20      (((v1_xboole_0 @ sk_A)
% 3.97/4.20        | (r2_hidden @ 
% 3.97/4.20           (k4_tarski @ (o_1_0_funct_1 @ sk_A) @ 
% 3.97/4.20            (k1_funct_1 @ sk_C_2 @ (o_1_0_funct_1 @ sk_A))) @ 
% 3.97/4.20           sk_C_2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['54', '62'])).
% 3.97/4.20  thf('64', plain,
% 3.97/4.20      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.97/4.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.97/4.20  thf('65', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C_2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['63', '64'])).
% 3.97/4.20  thf('66', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 3.97/4.20      inference('clc', [status(thm)], ['51', '65'])).
% 3.97/4.20  thf('67', plain,
% 3.97/4.20      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['32', '45'])).
% 3.97/4.20  thf(cc4_relset_1, axiom,
% 3.97/4.20    (![A:$i,B:$i]:
% 3.97/4.20     ( ( v1_xboole_0 @ A ) =>
% 3.97/4.20       ( ![C:$i]:
% 3.97/4.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 3.97/4.20           ( v1_xboole_0 @ C ) ) ) ))).
% 3.97/4.20  thf('68', plain,
% 3.97/4.20      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.97/4.20         (~ (v1_xboole_0 @ X30)
% 3.97/4.20          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 3.97/4.20          | (v1_xboole_0 @ X31))),
% 3.97/4.20      inference('cnf', [status(esa)], [cc4_relset_1])).
% 3.97/4.20  thf('69', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['67', '68'])).
% 3.97/4.20  thf(d1_funct_2, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.20       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.97/4.20           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.97/4.20             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.97/4.20         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.97/4.20           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.97/4.20             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.97/4.20  thf(zf_stmt_4, axiom,
% 3.97/4.20    (![B:$i,A:$i]:
% 3.97/4.20     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.97/4.20       ( zip_tseitin_0 @ B @ A ) ))).
% 3.97/4.20  thf('70', plain,
% 3.97/4.20      (![X45 : $i, X46 : $i]:
% 3.97/4.20         ((zip_tseitin_0 @ X45 @ X46) | ((X45) = (k1_xboole_0)))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_4])).
% 3.97/4.20  thf('71', plain,
% 3.97/4.20      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['32', '45'])).
% 3.97/4.20  thf(zf_stmt_5, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.97/4.20  thf(zf_stmt_6, axiom,
% 3.97/4.20    (![C:$i,B:$i,A:$i]:
% 3.97/4.20     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.97/4.20       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.97/4.20  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $o).
% 3.97/4.20  thf(zf_stmt_8, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.20       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.97/4.20         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.97/4.20           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.97/4.20             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.97/4.20  thf('72', plain,
% 3.97/4.20      (![X50 : $i, X51 : $i, X52 : $i]:
% 3.97/4.20         (~ (zip_tseitin_0 @ X50 @ X51)
% 3.97/4.20          | (zip_tseitin_1 @ X52 @ X50 @ X51)
% 3.97/4.20          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50))))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_8])).
% 3.97/4.20  thf('73', plain,
% 3.97/4.20      (((zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 3.97/4.20        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['71', '72'])).
% 3.97/4.20  thf('74', plain,
% 3.97/4.20      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['32', '45'])).
% 3.97/4.20  thf(redefinition_k1_relset_1, axiom,
% 3.97/4.20    (![A:$i,B:$i,C:$i]:
% 3.97/4.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.20       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.97/4.20  thf('75', plain,
% 3.97/4.20      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.97/4.20         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 3.97/4.20          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 3.97/4.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.97/4.20  thf('76', plain,
% 3.97/4.20      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['74', '75'])).
% 3.97/4.20  thf('77', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 3.97/4.20      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.20  thf('78', plain, (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_C_2) = (sk_A))),
% 3.97/4.20      inference('demod', [status(thm)], ['76', '77'])).
% 3.97/4.20  thf('79', plain,
% 3.97/4.20      (![X47 : $i, X48 : $i, X49 : $i]:
% 3.97/4.20         (((X47) != (k1_relset_1 @ X47 @ X48 @ X49))
% 3.97/4.20          | (v1_funct_2 @ X49 @ X47 @ X48)
% 3.97/4.20          | ~ (zip_tseitin_1 @ X49 @ X48 @ X47))),
% 3.97/4.20      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.97/4.20  thf('80', plain,
% 3.97/4.20      ((((sk_A) != (sk_A))
% 3.97/4.20        | ~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)
% 3.97/4.20        | (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2))),
% 3.97/4.20      inference('sup-', [status(thm)], ['78', '79'])).
% 3.97/4.20  thf('81', plain,
% 3.97/4.20      (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)
% 3.97/4.20        | ~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A))),
% 3.97/4.20      inference('simplify', [status(thm)], ['80'])).
% 3.97/4.20  thf('82', plain,
% 3.97/4.20      ((~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2))
% 3.97/4.20         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)))),
% 3.97/4.20      inference('split', [status(esa)], ['12'])).
% 3.97/4.20  thf('83', plain, (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2))),
% 3.97/4.20      inference('sat_resolution*', [status(thm)], ['28', '48', '49'])).
% 3.97/4.20  thf('84', plain, (~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_2)),
% 3.97/4.20      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 3.97/4.20  thf('85', plain, (~ (zip_tseitin_1 @ sk_C_2 @ sk_B_2 @ sk_A)),
% 3.97/4.20      inference('clc', [status(thm)], ['81', '84'])).
% 3.97/4.20  thf('86', plain, (~ (zip_tseitin_0 @ sk_B_2 @ sk_A)),
% 3.97/4.20      inference('clc', [status(thm)], ['73', '85'])).
% 3.97/4.20  thf('87', plain, (((sk_B_2) = (k1_xboole_0))),
% 3.97/4.20      inference('sup-', [status(thm)], ['70', '86'])).
% 3.97/4.20  thf(t4_subset_1, axiom,
% 3.97/4.20    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.97/4.20  thf('88', plain,
% 3.97/4.20      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 3.97/4.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.97/4.20  thf('89', plain,
% 3.97/4.20      (![X11 : $i, X12 : $i]:
% 3.97/4.20         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 3.97/4.20      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.20  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 3.97/4.20      inference('sup-', [status(thm)], ['88', '89'])).
% 3.97/4.20  thf('91', plain,
% 3.97/4.20      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.97/4.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.97/4.20  thf(t7_ordinal1, axiom,
% 3.97/4.20    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.97/4.20  thf('92', plain,
% 3.97/4.20      (![X28 : $i, X29 : $i]:
% 3.97/4.20         (~ (r2_hidden @ X28 @ X29) | ~ (r1_tarski @ X29 @ X28))),
% 3.97/4.20      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.97/4.20  thf('93', plain,
% 3.97/4.20      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 3.97/4.20      inference('sup-', [status(thm)], ['91', '92'])).
% 3.97/4.20  thf('94', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.97/4.20      inference('sup-', [status(thm)], ['90', '93'])).
% 3.97/4.20  thf('95', plain, ((v1_xboole_0 @ sk_C_2)),
% 3.97/4.20      inference('demod', [status(thm)], ['69', '87', '94'])).
% 3.97/4.20  thf('96', plain, ($false), inference('demod', [status(thm)], ['66', '95'])).
% 3.97/4.20  
% 3.97/4.20  % SZS output end Refutation
% 3.97/4.20  
% 3.97/4.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

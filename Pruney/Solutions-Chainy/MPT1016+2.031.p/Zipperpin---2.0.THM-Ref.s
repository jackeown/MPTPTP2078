%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vU67BMDtzH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  130 (1689 expanded)
%              Number of leaves         :   27 ( 488 expanded)
%              Depth                    :   31
%              Number of atoms          : 1854 (30047 expanded)
%              Number of equality atoms :  181 (2215 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t77_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
      <=> ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_C @ sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C @ sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( sk_C != sk_D_1 )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_C != sk_D_1 )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( ( k1_funct_1 @ sk_B @ X15 )
       != ( k1_funct_1 @ sk_B @ X14 ) )
      | ~ ( r2_hidden @ X14 @ sk_A )
      | ~ ( r2_hidden @ X15 @ sk_A )
      | ( v2_funct_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf(t25_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ C @ A @ B )
        & ( v1_funct_1 @ C ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( v2_funct_1 @ C )
        <=> ! [D: $i,E: $i] :
              ( ( ( ( k1_funct_1 @ C @ D )
                  = ( k1_funct_1 @ C @ E ) )
                & ( r2_hidden @ E @ A )
                & ( r2_hidden @ D @ A ) )
             => ( D = E ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ A )
     => ( ( v2_funct_1 @ C )
      <=> ! [D: $i,E: $i] :
            ( ( zip_tseitin_1 @ E @ D @ C @ A )
           => ( D = E ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [E: $i,D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_1 @ E @ D @ C @ A )
    <=> ( ( r2_hidden @ D @ A )
        & ( r2_hidden @ E @ A )
        & ( ( k1_funct_1 @ C @ D )
          = ( k1_funct_1 @ C @ E ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( zip_tseitin_0 @ B @ A )
       => ( zip_tseitin_2 @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( zip_tseitin_0 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_funct_2 @ X13 @ X12 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) ) )
      | ( zip_tseitin_2 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('13',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_A )
   <= ( r2_hidden @ sk_D_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( r2_hidden @ sk_C @ sk_A )
   <= ( r2_hidden @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_C )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('21',plain,(
    ! [X2: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X6 )
      | ( ( k1_funct_1 @ X5 @ X2 )
       != ( k1_funct_1 @ X5 @ X4 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k1_funct_1 @ sk_B @ sk_C )
         != ( k1_funct_1 @ sk_B @ X0 ) )
        | ~ ( r2_hidden @ sk_D_1 @ X1 )
        | ~ ( r2_hidden @ X0 @ X1 )
        | ( zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ X1 ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_C )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_C @ X0 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_C )
      = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ),
    inference(eq_res,[status(thm)],['22'])).

thf('24',plain,
    ( ( ~ ( r2_hidden @ sk_D_1 @ sk_A )
      | ( zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A ) )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( X10 = X9 )
      | ~ ( zip_tseitin_1 @ X9 @ X10 @ X8 @ X7 )
      | ~ ( zip_tseitin_2 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ( ~ ( zip_tseitin_2 @ sk_B @ sk_A )
      | ( sk_D_1 = sk_C )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_B )
      | ( sk_D_1 = sk_C ) )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,
    ( ( ( sk_D_1 = sk_C )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( v2_funct_1 @ sk_B )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('31',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_A @ k1_xboole_0 )
      | ( sk_D_1 = sk_C )
      | ( zip_tseitin_2 @ sk_B @ sk_A ) )
   <= ( ( v2_funct_1 @ sk_B )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( sk_D_1 = sk_C )
      | ( zip_tseitin_2 @ sk_B @ sk_A ) )
   <= ( ( v2_funct_1 @ sk_B )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['31','33'])).

thf('35',plain,
    ( ( ~ ( zip_tseitin_2 @ sk_B @ sk_A )
      | ( sk_D_1 = sk_C )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ( ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('36',plain,
    ( ( ( sk_D_1 = sk_C )
      | ~ ( v2_funct_1 @ sk_B )
      | ( sk_D_1 = sk_C ) )
   <= ( ( v2_funct_1 @ sk_B )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('38',plain,
    ( ( ( sk_D_1 = sk_C )
      | ( sk_D_1 = sk_C ) )
   <= ( ( v2_funct_1 @ sk_B )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_D_1 = sk_C )
   <= ( ( v2_funct_1 @ sk_B )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( sk_C != sk_D_1 )
   <= ( sk_C != sk_D_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('41',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != sk_D_1 )
      & ( v2_funct_1 @ sk_B )
      & ( r2_hidden @ sk_C @ sk_A )
      & ( r2_hidden @ sk_D_1 @ sk_A )
      & ( ( k1_funct_1 @ sk_B @ sk_C )
        = ( k1_funct_1 @ sk_B @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_C )
     != ( k1_funct_1 @ sk_B @ sk_D_1 ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C @ sk_A )
    | ~ ( r2_hidden @ sk_D_1 @ sk_A )
    | ( sk_C = sk_D_1 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) )
    | ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ ( sk_E @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) @ X8 @ X7 )
      | ( v2_funct_1 @ X8 )
      | ~ ( zip_tseitin_2 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v2_funct_1 @ sk_B )
    | ( zip_tseitin_1 @ ( sk_E @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v2_funct_1 @ sk_B )
    | ( zip_tseitin_1 @ ( sk_E @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X3 )
      | ~ ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('51',plain,
    ( ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v2_funct_1 @ sk_B )
    | ( zip_tseitin_1 @ ( sk_E @ sk_A @ sk_B ) @ ( sk_D @ sk_A @ sk_B ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('53',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_funct_1 @ X5 @ X2 )
        = ( k1_funct_1 @ X5 @ X4 ) )
      | ~ ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_E @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ X0 )
         != ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ sk_B ) ) )
        | ( sk_A = k1_xboole_0 )
        | ( v2_funct_1 @ sk_B )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_E @ sk_A @ sk_B ) @ sk_A )
        | ( X0
          = ( sk_E @ sk_A @ sk_B ) ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( v2_funct_1 @ sk_B )
        | ( X0
          = ( sk_E @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B )
        | ( sk_A = k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_B @ X0 )
         != ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ sk_B ) ) ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ X0 )
         != ( k1_funct_1 @ sk_B @ ( sk_D @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_E @ sk_A @ sk_B ) )
        | ( v2_funct_1 @ sk_B )
        | ( sk_A = k1_xboole_0 ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ sk_B )
      | ( ( sk_D @ sk_A @ sk_B )
        = ( sk_E @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_A @ sk_B ) @ sk_A ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ sk_B )
      | ( ( sk_D @ sk_A @ sk_B )
        = ( sk_E @ sk_A @ sk_B ) )
      | ( v2_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','59'])).

thf('61',plain,
    ( ( ( ( sk_D @ sk_A @ sk_B )
        = ( sk_E @ sk_A @ sk_B ) )
      | ( v2_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( sk_D @ X7 @ X8 )
       != ( sk_E @ X7 @ X8 ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( zip_tseitin_2 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,
    ( ( ( ( sk_D @ sk_A @ sk_B )
       != ( sk_D @ sk_A @ sk_B ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ sk_B )
      | ~ ( zip_tseitin_2 @ sk_B @ sk_A )
      | ( v2_funct_1 @ sk_B ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( zip_tseitin_2 @ sk_B @ sk_A )
      | ( v2_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('66',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ sk_B ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v2_funct_1 @ sk_B )
   <= ~ ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( zip_tseitin_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('70',plain,
    ( ( ~ ( zip_tseitin_0 @ sk_A @ k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_B @ sk_A ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('72',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('74',plain,
    ( ( zip_tseitin_2 @ sk_B @ k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X7: $i,X8: $i] :
      ( ( zip_tseitin_1 @ ( sk_E @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) @ X8 @ X7 )
      | ( v2_funct_1 @ X8 )
      | ~ ( zip_tseitin_2 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('76',plain,
    ( ( ( v2_funct_1 @ sk_B )
      | ( zip_tseitin_1 @ ( sk_E @ k1_xboole_0 @ sk_B ) @ ( sk_D @ k1_xboole_0 @ sk_B ) @ sk_B @ k1_xboole_0 ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v2_funct_1 @ sk_B )
   <= ~ ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( zip_tseitin_1 @ ( sk_E @ k1_xboole_0 @ sk_B ) @ ( sk_D @ k1_xboole_0 @ sk_B ) @ sk_B @ k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_funct_1 @ X5 @ X2 )
        = ( k1_funct_1 @ X5 @ X4 ) )
      | ~ ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_D @ k1_xboole_0 @ sk_B ) )
      = ( k1_funct_1 @ sk_B @ ( sk_E @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) )
   <= ! [X14: $i,X15: $i] :
        ( ( X15 = X14 )
        | ( ( k1_funct_1 @ sk_B @ X15 )
         != ( k1_funct_1 @ sk_B @ X14 ) )
        | ~ ( r2_hidden @ X14 @ sk_A )
        | ~ ( r2_hidden @ X15 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ X0 )
         != ( k1_funct_1 @ sk_B @ ( sk_D @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_E @ k1_xboole_0 @ sk_B ) @ sk_A )
        | ( X0
          = ( sk_E @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('84',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ ( sk_E @ k1_xboole_0 @ sk_B ) @ ( sk_D @ k1_xboole_0 @ sk_B ) @ sk_B @ k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('86',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X3 )
      | ~ ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ X0 )
         != ( k1_funct_1 @ sk_B @ ( sk_D @ k1_xboole_0 @ sk_B ) ) )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( X0
          = ( sk_E @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','87'])).

thf('89',plain,
    ( ( ( ( sk_D @ k1_xboole_0 @ sk_B )
        = ( sk_E @ k1_xboole_0 @ sk_B ) )
      | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(eq_res,[status(thm)],['88'])).

thf('90',plain,
    ( ( zip_tseitin_1 @ ( sk_E @ k1_xboole_0 @ sk_B ) @ ( sk_D @ k1_xboole_0 @ sk_B ) @ sk_B @ k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('91',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( zip_tseitin_1 @ X4 @ X2 @ X5 @ X3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('92',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ sk_B ) @ k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( sk_D @ k1_xboole_0 @ sk_B )
      = ( sk_E @ k1_xboole_0 @ sk_B ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( sk_D @ X7 @ X8 )
       != ( sk_E @ X7 @ X8 ) )
      | ( v2_funct_1 @ X8 )
      | ~ ( zip_tseitin_2 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('95',plain,
    ( ( ( ( sk_D @ k1_xboole_0 @ sk_B )
       != ( sk_D @ k1_xboole_0 @ sk_B ) )
      | ~ ( zip_tseitin_2 @ sk_B @ k1_xboole_0 )
      | ( v2_funct_1 @ sk_B ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( zip_tseitin_2 @ sk_B @ k1_xboole_0 )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('97',plain,
    ( ( ( ( sk_D @ k1_xboole_0 @ sk_B )
       != ( sk_D @ k1_xboole_0 @ sk_B ) )
      | ( v2_funct_1 @ sk_B ) )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ( ~ ( v2_funct_1 @ sk_B )
      & ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ~ ( v2_funct_1 @ sk_B )
   <= ~ ( v2_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ! [X14: $i,X15: $i] :
          ( ( X15 = X14 )
          | ( ( k1_funct_1 @ sk_B @ X15 )
           != ( k1_funct_1 @ sk_B @ X14 ) )
          | ~ ( r2_hidden @ X14 @ sk_A )
          | ~ ( r2_hidden @ X15 @ sk_A ) )
    | ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','42','43','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vU67BMDtzH
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 156 iterations in 0.051s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.22/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(t77_funct_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ B ) <=>
% 0.22/0.52         ( ![C:$i,D:$i]:
% 0.22/0.52           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.52               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.52             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52          ( ( v2_funct_1 @ B ) <=>
% 0.22/0.52            ( ![C:$i,D:$i]:
% 0.22/0.52              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.52                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.52                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.22/0.52  thf('0', plain, (((r2_hidden @ sk_C @ sk_A) | ~ (v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain, (((r2_hidden @ sk_C @ sk_A)) | ~ ((v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('2', plain, (((r2_hidden @ sk_D_1 @ sk_A) | ~ (v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain, (((r2_hidden @ sk_D_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))
% 0.22/0.52        | ~ (v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))) | 
% 0.22/0.52       ~ ((v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('split', [status(esa)], ['4'])).
% 0.22/0.52  thf('6', plain, ((((sk_C) != (sk_D_1)) | ~ (v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain, (~ (((sk_C) = (sk_D_1))) | ~ ((v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('split', [status(esa)], ['6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         (((X15) = (X14))
% 0.22/0.52          | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52          | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52          | ~ (r2_hidden @ X15 @ sk_A)
% 0.22/0.52          | (v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('9', plain, (((v2_funct_1 @ sk_B)) <= (((v2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['8'])).
% 0.22/0.52  thf(t25_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.52         ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.52         ( ( v2_funct_1 @ C ) <=>
% 0.22/0.52           ( ![D:$i,E:$i]:
% 0.22/0.52             ( ( ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) & 
% 0.22/0.52                 ( r2_hidden @ E @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.22/0.52               ( ( D ) = ( E ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_1, axiom,
% 0.22/0.52    (![B:$i,A:$i]:
% 0.22/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.52       ( zip_tseitin_0 @ B @ A ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((zip_tseitin_0 @ X0 @ X1) | ((X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $o).
% 0.22/0.52  thf(zf_stmt_3, axiom,
% 0.22/0.52    (![C:$i,A:$i]:
% 0.22/0.52     ( ( zip_tseitin_2 @ C @ A ) =>
% 0.22/0.52       ( ( v2_funct_1 @ C ) <=>
% 0.22/0.52         ( ![D:$i,E:$i]:
% 0.22/0.52           ( ( zip_tseitin_1 @ E @ D @ C @ A ) => ( ( D ) = ( E ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.22/0.52  thf(zf_stmt_5, axiom,
% 0.22/0.52    (![E:$i,D:$i,C:$i,A:$i]:
% 0.22/0.52     ( ( zip_tseitin_1 @ E @ D @ C @ A ) <=>
% 0.22/0.52       ( ( r2_hidden @ D @ A ) & ( r2_hidden @ E @ A ) & 
% 0.22/0.52         ( ( k1_funct_1 @ C @ D ) = ( k1_funct_1 @ C @ E ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $o).
% 0.22/0.52  thf(zf_stmt_7, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_2 @ C @ A ) ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (zip_tseitin_0 @ X11 @ X12)
% 0.22/0.52          | ~ (v1_funct_1 @ X13)
% 0.22/0.52          | ~ (v1_funct_2 @ X13 @ X12 @ X11)
% 0.22/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11)))
% 0.22/0.52          | (zip_tseitin_2 @ X13 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (((zip_tseitin_2 @ sk_B @ sk_A)
% 0.22/0.52        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.52        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.52        | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.52  thf('14', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((zip_tseitin_2 @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((r2_hidden @ sk_D_1 @ sk_A)) <= (((r2_hidden @ sk_D_1 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((r2_hidden @ sk_C @ sk_A)) <= (((r2_hidden @ sk_C @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1)))
% 0.22/0.52         <= ((((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('split', [status(esa)], ['4'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X2 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         ((zip_tseitin_1 @ X4 @ X2 @ X5 @ X6)
% 0.22/0.52          | ((k1_funct_1 @ X5 @ X2) != (k1_funct_1 @ X5 @ X4))
% 0.22/0.52          | ~ (r2_hidden @ X4 @ X6)
% 0.22/0.52          | ~ (r2_hidden @ X2 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((![X0 : $i, X1 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B @ sk_C) != (k1_funct_1 @ sk_B @ X0))
% 0.22/0.52           | ~ (r2_hidden @ sk_D_1 @ X1)
% 0.22/0.52           | ~ (r2_hidden @ X0 @ X1)
% 0.22/0.52           | (zip_tseitin_1 @ X0 @ sk_D_1 @ sk_B @ X1)))
% 0.22/0.52         <= ((((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ X0)
% 0.22/0.52           | ~ (r2_hidden @ sk_C @ X0)
% 0.22/0.52           | ~ (r2_hidden @ sk_D_1 @ X0)))
% 0.22/0.52         <= ((((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (((~ (r2_hidden @ sk_D_1 @ sk_A)
% 0.22/0.52         | (zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A)))
% 0.22/0.52         <= (((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (((zip_tseitin_1 @ sk_C @ sk_D_1 @ sk_B @ sk_A))
% 0.22/0.52         <= (((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X8)
% 0.22/0.52          | ((X10) = (X9))
% 0.22/0.52          | ~ (zip_tseitin_1 @ X9 @ X10 @ X8 @ X7)
% 0.22/0.52          | ~ (zip_tseitin_2 @ X8 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (((~ (zip_tseitin_2 @ sk_B @ sk_A)
% 0.22/0.52         | ((sk_D_1) = (sk_C))
% 0.22/0.52         | ~ (v2_funct_1 @ sk_B)))
% 0.22/0.52         <= (((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0)) | ~ (v2_funct_1 @ sk_B) | ((sk_D_1) = (sk_C))))
% 0.22/0.52         <= (((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (((((sk_D_1) = (sk_C)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (((zip_tseitin_2 @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (((~ (zip_tseitin_0 @ sk_A @ k1_xboole_0)
% 0.22/0.52         | ((sk_D_1) = (sk_C))
% 0.22/0.52         | (zip_tseitin_2 @ sk_B @ sk_A)))
% 0.22/0.52         <= (((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((zip_tseitin_0 @ X0 @ X1) | ((X1) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('33', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ k1_xboole_0)),
% 0.22/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (((((sk_D_1) = (sk_C)) | (zip_tseitin_2 @ sk_B @ sk_A)))
% 0.22/0.52         <= (((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (((~ (zip_tseitin_2 @ sk_B @ sk_A)
% 0.22/0.52         | ((sk_D_1) = (sk_C))
% 0.22/0.52         | ~ (v2_funct_1 @ sk_B)))
% 0.22/0.52         <= (((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (((((sk_D_1) = (sk_C)) | ~ (v2_funct_1 @ sk_B) | ((sk_D_1) = (sk_C))))
% 0.22/0.52         <= (((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain, (((v2_funct_1 @ sk_B)) <= (((v2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['8'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (((((sk_D_1) = (sk_C)) | ((sk_D_1) = (sk_C))))
% 0.22/0.52         <= (((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      ((((sk_D_1) = (sk_C)))
% 0.22/0.52         <= (((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.52  thf('40', plain, ((((sk_C) != (sk_D_1))) <= (~ (((sk_C) = (sk_D_1))))),
% 0.22/0.52      inference('split', [status(esa)], ['6'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      ((((sk_C) != (sk_C)))
% 0.22/0.52         <= (~ (((sk_C) = (sk_D_1))) & 
% 0.22/0.52             ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             ((r2_hidden @ sk_C @ sk_A)) & 
% 0.22/0.52             ((r2_hidden @ sk_D_1 @ sk_A)) & 
% 0.22/0.52             (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (~ (((k1_funct_1 @ sk_B @ sk_C) = (k1_funct_1 @ sk_B @ sk_D_1))) | 
% 0.22/0.52       ~ ((v2_funct_1 @ sk_B)) | ~ ((r2_hidden @ sk_C @ sk_A)) | 
% 0.22/0.52       ~ ((r2_hidden @ sk_D_1 @ sk_A)) | (((sk_C) = (sk_D_1)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      ((![X14 : $i, X15 : $i]:
% 0.22/0.52          (((X15) = (X14))
% 0.22/0.52           | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52           | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ X15 @ sk_A))) | 
% 0.22/0.52       ((v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('split', [status(esa)], ['8'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '16'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((zip_tseitin_1 @ (sk_E @ X7 @ X8) @ (sk_D @ X7 @ X8) @ X8 @ X7)
% 0.22/0.52          | (v2_funct_1 @ X8)
% 0.22/0.52          | ~ (zip_tseitin_2 @ X8 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | (v2_funct_1 @ sk_B)
% 0.22/0.52        | (zip_tseitin_1 @ (sk_E @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B) @ 
% 0.22/0.52           sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((r2_hidden @ X2 @ X3) | ~ (zip_tseitin_1 @ X4 @ X2 @ X5 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B)
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | (r2_hidden @ (sk_D @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | (v2_funct_1 @ sk_B)
% 0.22/0.52        | (zip_tseitin_1 @ (sk_E @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B) @ 
% 0.22/0.52           sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((r2_hidden @ X4 @ X3) | ~ (zip_tseitin_1 @ X4 @ X2 @ X5 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B)
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | (r2_hidden @ (sk_E @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | (v2_funct_1 @ sk_B)
% 0.22/0.52        | (zip_tseitin_1 @ (sk_E @ sk_A @ sk_B) @ (sk_D @ sk_A @ sk_B) @ 
% 0.22/0.52           sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         (((k1_funct_1 @ X5 @ X2) = (k1_funct_1 @ X5 @ X4))
% 0.22/0.52          | ~ (zip_tseitin_1 @ X4 @ X2 @ X5 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B)
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((k1_funct_1 @ sk_B @ (sk_D @ sk_A @ sk_B))
% 0.22/0.52            = (k1_funct_1 @ sk_B @ (sk_E @ sk_A @ sk_B))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      ((![X14 : $i, X15 : $i]:
% 0.22/0.52          (((X15) = (X14))
% 0.22/0.52           | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52           | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ X15 @ sk_A)))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['8'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B @ X0)
% 0.22/0.52             != (k1_funct_1 @ sk_B @ (sk_D @ sk_A @ sk_B)))
% 0.22/0.52           | ((sk_A) = (k1_xboole_0))
% 0.22/0.52           | (v2_funct_1 @ sk_B)
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ (sk_E @ sk_A @ sk_B) @ sk_A)
% 0.22/0.52           | ((X0) = (sk_E @ sk_A @ sk_B))))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((sk_A) = (k1_xboole_0))
% 0.22/0.52           | (v2_funct_1 @ sk_B)
% 0.22/0.52           | ((X0) = (sk_E @ sk_A @ sk_B))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | (v2_funct_1 @ sk_B)
% 0.22/0.52           | ((sk_A) = (k1_xboole_0))
% 0.22/0.52           | ((k1_funct_1 @ sk_B @ X0)
% 0.22/0.52               != (k1_funct_1 @ sk_B @ (sk_D @ sk_A @ sk_B)))))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['51', '56'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B @ X0)
% 0.22/0.52             != (k1_funct_1 @ sk_B @ (sk_D @ sk_A @ sk_B)))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | ((X0) = (sk_E @ sk_A @ sk_B))
% 0.22/0.52           | (v2_funct_1 @ sk_B)
% 0.22/0.52           | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0))
% 0.22/0.52         | (v2_funct_1 @ sk_B)
% 0.22/0.52         | ((sk_D @ sk_A @ sk_B) = (sk_E @ sk_A @ sk_B))
% 0.22/0.52         | ~ (r2_hidden @ (sk_D @ sk_A @ sk_B) @ sk_A)))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['58'])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0))
% 0.22/0.52         | (v2_funct_1 @ sk_B)
% 0.22/0.52         | ((sk_D @ sk_A @ sk_B) = (sk_E @ sk_A @ sk_B))
% 0.22/0.52         | (v2_funct_1 @ sk_B)
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['48', '59'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (((((sk_D @ sk_A @ sk_B) = (sk_E @ sk_A @ sk_B))
% 0.22/0.52         | (v2_funct_1 @ sk_B)
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['60'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         (((sk_D @ X7 @ X8) != (sk_E @ X7 @ X8))
% 0.22/0.52          | (v2_funct_1 @ X8)
% 0.22/0.52          | ~ (zip_tseitin_2 @ X8 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      (((((sk_D @ sk_A @ sk_B) != (sk_D @ sk_A @ sk_B))
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))
% 0.22/0.52         | (v2_funct_1 @ sk_B)
% 0.22/0.52         | ~ (zip_tseitin_2 @ sk_B @ sk_A)
% 0.22/0.52         | (v2_funct_1 @ sk_B)))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (((~ (zip_tseitin_2 @ sk_B @ sk_A)
% 0.22/0.52         | (v2_funct_1 @ sk_B)
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['63'])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '16'])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0)) | (v2_funct_1 @ sk_B)))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('clc', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('67', plain, ((~ (v2_funct_1 @ sk_B)) <= (~ ((v2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (((zip_tseitin_2 @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_A @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      (((~ (zip_tseitin_0 @ sk_A @ k1_xboole_0) | (zip_tseitin_2 @ sk_B @ sk_A)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.52  thf('72', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ k1_xboole_0)),
% 0.22/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.52  thf('73', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      (((zip_tseitin_2 @ sk_B @ k1_xboole_0))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.22/0.52  thf('75', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((zip_tseitin_1 @ (sk_E @ X7 @ X8) @ (sk_D @ X7 @ X8) @ X8 @ X7)
% 0.22/0.52          | (v2_funct_1 @ X8)
% 0.22/0.52          | ~ (zip_tseitin_2 @ X8 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      ((((v2_funct_1 @ sk_B)
% 0.22/0.52         | (zip_tseitin_1 @ (sk_E @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.52            (sk_D @ k1_xboole_0 @ sk_B) @ sk_B @ k1_xboole_0)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.52  thf('77', plain, ((~ (v2_funct_1 @ sk_B)) <= (~ ((v2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      (((zip_tseitin_1 @ (sk_E @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.52         (sk_D @ k1_xboole_0 @ sk_B) @ sk_B @ k1_xboole_0))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('clc', [status(thm)], ['76', '77'])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         (((k1_funct_1 @ X5 @ X2) = (k1_funct_1 @ X5 @ X4))
% 0.22/0.52          | ~ (zip_tseitin_1 @ X4 @ X2 @ X5 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      ((((k1_funct_1 @ sk_B @ (sk_D @ k1_xboole_0 @ sk_B))
% 0.22/0.52          = (k1_funct_1 @ sk_B @ (sk_E @ k1_xboole_0 @ sk_B))))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.52  thf('81', plain,
% 0.22/0.52      ((![X14 : $i, X15 : $i]:
% 0.22/0.52          (((X15) = (X14))
% 0.22/0.52           | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52           | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ X15 @ sk_A)))
% 0.22/0.52         <= ((![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['8'])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B @ X0)
% 0.22/0.52             != (k1_funct_1 @ sk_B @ (sk_D @ k1_xboole_0 @ sk_B)))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ (sk_E @ k1_xboole_0 @ sk_B) @ sk_A)
% 0.22/0.52           | ((X0) = (sk_E @ k1_xboole_0 @ sk_B))))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (((zip_tseitin_1 @ (sk_E @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.52         (sk_D @ k1_xboole_0 @ sk_B) @ sk_B @ k1_xboole_0))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('clc', [status(thm)], ['76', '77'])).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((r2_hidden @ X4 @ X3) | ~ (zip_tseitin_1 @ X4 @ X2 @ X5 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.52  thf('87', plain,
% 0.22/0.52      (((r2_hidden @ (sk_E @ k1_xboole_0 @ sk_B) @ k1_xboole_0))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((k1_funct_1 @ sk_B @ X0)
% 0.22/0.52             != (k1_funct_1 @ sk_B @ (sk_D @ k1_xboole_0 @ sk_B)))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.52           | ((X0) = (sk_E @ k1_xboole_0 @ sk_B))))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['82', '83', '84', '87'])).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      (((((sk_D @ k1_xboole_0 @ sk_B) = (sk_E @ k1_xboole_0 @ sk_B))
% 0.22/0.52         | ~ (r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B) @ k1_xboole_0)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['88'])).
% 0.22/0.52  thf('90', plain,
% 0.22/0.52      (((zip_tseitin_1 @ (sk_E @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.52         (sk_D @ k1_xboole_0 @ sk_B) @ sk_B @ k1_xboole_0))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('clc', [status(thm)], ['76', '77'])).
% 0.22/0.52  thf('91', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((r2_hidden @ X2 @ X3) | ~ (zip_tseitin_1 @ X4 @ X2 @ X5 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      (((r2_hidden @ (sk_D @ k1_xboole_0 @ sk_B) @ k1_xboole_0))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['90', '91'])).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      ((((sk_D @ k1_xboole_0 @ sk_B) = (sk_E @ k1_xboole_0 @ sk_B)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['89', '92'])).
% 0.22/0.52  thf('94', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         (((sk_D @ X7 @ X8) != (sk_E @ X7 @ X8))
% 0.22/0.52          | (v2_funct_1 @ X8)
% 0.22/0.52          | ~ (zip_tseitin_2 @ X8 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (((((sk_D @ k1_xboole_0 @ sk_B) != (sk_D @ k1_xboole_0 @ sk_B))
% 0.22/0.52         | ~ (zip_tseitin_2 @ sk_B @ k1_xboole_0)
% 0.22/0.52         | (v2_funct_1 @ sk_B)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['93', '94'])).
% 0.22/0.52  thf('96', plain,
% 0.22/0.52      (((zip_tseitin_2 @ sk_B @ k1_xboole_0))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.22/0.52  thf('97', plain,
% 0.22/0.52      (((((sk_D @ k1_xboole_0 @ sk_B) != (sk_D @ k1_xboole_0 @ sk_B))
% 0.22/0.52         | (v2_funct_1 @ sk_B)))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['95', '96'])).
% 0.22/0.52  thf('98', plain,
% 0.22/0.52      (((v2_funct_1 @ sk_B))
% 0.22/0.52         <= (~ ((v2_funct_1 @ sk_B)) & 
% 0.22/0.52             (![X14 : $i, X15 : $i]:
% 0.22/0.52                (((X15) = (X14))
% 0.22/0.52                 | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52                 | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52                 | ~ (r2_hidden @ X15 @ sk_A))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['97'])).
% 0.22/0.52  thf('99', plain, ((~ (v2_funct_1 @ sk_B)) <= (~ ((v2_funct_1 @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('100', plain,
% 0.22/0.52      (~
% 0.22/0.52       (![X14 : $i, X15 : $i]:
% 0.22/0.52          (((X15) = (X14))
% 0.22/0.52           | ((k1_funct_1 @ sk_B @ X15) != (k1_funct_1 @ sk_B @ X14))
% 0.22/0.52           | ~ (r2_hidden @ X14 @ sk_A)
% 0.22/0.52           | ~ (r2_hidden @ X15 @ sk_A))) | 
% 0.22/0.52       ((v2_funct_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['98', '99'])).
% 0.22/0.52  thf('101', plain, ($false),
% 0.22/0.52      inference('sat_resolution*', [status(thm)],
% 0.22/0.52                ['1', '3', '5', '7', '42', '43', '100'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

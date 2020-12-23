%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E6tChEamH4

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:55 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 719 expanded)
%              Number of leaves         :   33 ( 217 expanded)
%              Depth                    :   17
%              Number of atoms          :  681 (8357 expanded)
%              Number of equality atoms :   21 ( 338 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_1 @ D @ C @ B @ A ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_1 @ X24 @ X25 @ X26 @ X27 )
      | ( r2_hidden @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( X9
       != ( k1_funct_1 @ X5 @ X10 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('4',plain,(
    ! [X5: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X10 ) @ ( k2_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_1 @ X1 @ X3 @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    r2_hidden @ sk_C_2 @ ( k1_funct_2 @ sk_A @ sk_B ) ),
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

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X21 @ X18 @ X19 ) @ X21 @ X18 @ X19 )
      | ( X20
       != ( k1_funct_2 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('8',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X21 @ X18 @ X19 ) @ X21 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_funct_2 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B @ sk_A ) @ sk_C_2 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_2 @ sk_B @ sk_A ) @ sk_C_2 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13 = X11 )
      | ~ ( zip_tseitin_0 @ X11 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('12',plain,
    ( sk_C_2
    = ( sk_E_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( zip_tseitin_0 @ X11 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( zip_tseitin_1 @ X0 @ X2 @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( zip_tseitin_0 @ X11 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v1_funct_1 @ X11 )
      | ~ ( zip_tseitin_0 @ X11 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relat_1 @ X11 )
        = X14 )
      | ~ ( zip_tseitin_0 @ X11 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','21','24','27'])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relat_1 @ X32 )
       != X31 )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X32 @ X33 @ X31 ) @ X32 @ X33 @ X31 )
      | ( zip_tseitin_2 @ X32 @ X33 @ X31 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('31',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( zip_tseitin_2 @ X32 @ X33 @ ( k1_relat_1 @ X32 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_3 @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) @ X32 @ X33 @ ( k1_relat_1 @ X32 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_3 @ sk_C_2 @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) @ sk_C_2 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_2 @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('34',plain,
    ( ( k1_relat_1 @ sk_C_2 )
    = sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_3 @ sk_C_2 @ X0 @ sk_A ) @ sk_C_2 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_3 @ sk_C_2 @ X0 @ sk_A ) @ sk_C_2 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_D_3 @ sk_C_2 @ X0 @ sk_A ) ) @ sk_B )
      | ( zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_1 @ X24 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X25 @ X24 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D_3 @ sk_C_2 @ X0 @ sk_A ) @ sk_C_2 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_3 @ sk_C_2 @ X0 @ sk_A ) @ sk_C_2 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('43',plain,
    ( ( zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( zip_tseitin_2 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( $false
   <= ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_C_2 )
   <= ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['43'])).

thf('52',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( zip_tseitin_2 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('53',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('57',plain,(
    ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['50','55','56'])).

thf('58',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['47','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E6tChEamH4
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 117 iterations in 0.109s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.38/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.38/0.57  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(t121_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.57       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.57        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.57          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      ((~ (v1_funct_1 @ sk_C_2)
% 0.38/0.57        | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.38/0.57        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      ((~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((m1_subset_1 @ sk_C_2 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf(t5_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.38/0.57       ( ( ( ![D:$i]:
% 0.38/0.57             ( ( r2_hidden @ D @ A ) =>
% 0.38/0.57               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.38/0.57           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.38/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.57           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_1, axiom,
% 0.38/0.57    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.38/0.57       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.57         ((zip_tseitin_1 @ X24 @ X25 @ X26 @ X27) | (r2_hidden @ X24 @ X27))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf(d5_funct_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.38/0.57           ( ![C:$i]:
% 0.38/0.57             ( ( r2_hidden @ C @ B ) <=>
% 0.38/0.57               ( ?[D:$i]:
% 0.38/0.57                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.38/0.57                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      (![X5 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 0.38/0.57         (((X7) != (k2_relat_1 @ X5))
% 0.38/0.57          | (r2_hidden @ X9 @ X7)
% 0.38/0.57          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 0.38/0.57          | ((X9) != (k1_funct_1 @ X5 @ X10))
% 0.38/0.57          | ~ (v1_funct_1 @ X5)
% 0.38/0.57          | ~ (v1_relat_1 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X5 : $i, X10 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X5)
% 0.38/0.57          | ~ (v1_funct_1 @ X5)
% 0.38/0.57          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X5))
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ X5 @ X10) @ (k2_relat_1 @ X5)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['3'])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         ((zip_tseitin_1 @ X1 @ X3 @ X2 @ (k1_relat_1 @ X0))
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ (k2_relat_1 @ X0))
% 0.38/0.57          | ~ (v1_funct_1 @ X0)
% 0.38/0.57          | ~ (v1_relat_1 @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.57  thf('6', plain, ((r2_hidden @ sk_C_2 @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(d2_funct_2, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.57       ( ![D:$i]:
% 0.38/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57           ( ?[E:$i]:
% 0.38/0.57             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.38/0.57               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.38/0.57               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_3, axiom,
% 0.38/0.57    (![E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.38/0.57       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.38/0.57         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.38/0.57         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.38/0.57  thf(zf_stmt_4, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.57       ( ![D:$i]:
% 0.38/0.57         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.57           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X21 @ X20)
% 0.38/0.57          | (zip_tseitin_0 @ (sk_E_1 @ X21 @ X18 @ X19) @ X21 @ X18 @ X19)
% 0.38/0.57          | ((X20) != (k1_funct_2 @ X19 @ X18)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.38/0.57         ((zip_tseitin_0 @ (sk_E_1 @ X21 @ X18 @ X19) @ X21 @ X18 @ X19)
% 0.38/0.57          | ~ (r2_hidden @ X21 @ (k1_funct_2 @ X19 @ X18)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B @ sk_A) @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '8'])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_2 @ sk_B @ sk_A) @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['6', '8'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.57         (((X13) = (X11)) | ~ (zip_tseitin_0 @ X11 @ X13 @ X12 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.57  thf('12', plain, (((sk_C_2) = (sk_E_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.57         ((r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.38/0.57          | ~ (zip_tseitin_0 @ X11 @ X13 @ X12 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.57  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf(d3_tarski, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.57          | (r2_hidden @ X0 @ X2)
% 0.38/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ sk_C_2)
% 0.38/0.57          | ~ (v1_funct_1 @ sk_C_2)
% 0.38/0.57          | (zip_tseitin_1 @ X0 @ X2 @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['5', '17'])).
% 0.38/0.57  thf('19', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.57         ((v1_relat_1 @ X11) | ~ (zip_tseitin_0 @ X11 @ X13 @ X12 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.57  thf('21', plain, ((v1_relat_1 @ sk_C_2)),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.57         ((v1_funct_1 @ X11) | ~ (zip_tseitin_0 @ X11 @ X13 @ X12 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.57  thf('24', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain, ((zip_tseitin_0 @ sk_C_2 @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '12'])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X11) = (X14))
% 0.38/0.57          | ~ (zip_tseitin_0 @ X11 @ X13 @ X12 @ X14))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.57  thf('27', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         ((zip_tseitin_1 @ X0 @ X2 @ X1 @ sk_A)
% 0.38/0.57          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ sk_B))),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '21', '24', '27'])).
% 0.38/0.57  thf('29', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_6, axiom,
% 0.38/0.57    (![C:$i,B:$i,A:$i]:
% 0.38/0.57     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.38/0.57       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.38/0.57  thf(zf_stmt_8, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.57       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.38/0.57           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.38/0.57         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.57         (((k1_relat_1 @ X32) != (X31))
% 0.38/0.57          | ~ (zip_tseitin_1 @ (sk_D_3 @ X32 @ X33 @ X31) @ X32 @ X33 @ X31)
% 0.38/0.57          | (zip_tseitin_2 @ X32 @ X33 @ X31)
% 0.38/0.57          | ~ (v1_funct_1 @ X32)
% 0.38/0.57          | ~ (v1_relat_1 @ X32))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X32 : $i, X33 : $i]:
% 0.38/0.57         (~ (v1_relat_1 @ X32)
% 0.38/0.57          | ~ (v1_funct_1 @ X32)
% 0.38/0.57          | (zip_tseitin_2 @ X32 @ X33 @ (k1_relat_1 @ X32))
% 0.38/0.57          | ~ (zip_tseitin_1 @ (sk_D_3 @ X32 @ X33 @ (k1_relat_1 @ X32)) @ 
% 0.38/0.57               X32 @ X33 @ (k1_relat_1 @ X32)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (zip_tseitin_1 @ (sk_D_3 @ sk_C_2 @ X0 @ (k1_relat_1 @ sk_C_2)) @ 
% 0.38/0.57             sk_C_2 @ X0 @ sk_A)
% 0.38/0.57          | (zip_tseitin_2 @ sk_C_2 @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.38/0.57          | ~ (v1_funct_1 @ sk_C_2)
% 0.38/0.57          | ~ (v1_relat_1 @ sk_C_2))),
% 0.38/0.57      inference('sup-', [status(thm)], ['29', '31'])).
% 0.38/0.57  thf('33', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('34', plain, (((k1_relat_1 @ sk_C_2) = (sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (zip_tseitin_1 @ (sk_D_3 @ sk_C_2 @ X0 @ sk_A) @ sk_C_2 @ X0 @ sk_A)
% 0.38/0.57          | (zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A)
% 0.38/0.57          | ~ (v1_funct_1 @ sk_C_2)
% 0.38/0.57          | ~ (v1_relat_1 @ sk_C_2))),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.38/0.57  thf('36', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('37', plain, ((v1_relat_1 @ sk_C_2)),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (zip_tseitin_1 @ (sk_D_3 @ sk_C_2 @ X0 @ sk_A) @ sk_C_2 @ X0 @ sk_A)
% 0.38/0.57          | (zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_D_3 @ sk_C_2 @ X0 @ sk_A)) @ 
% 0.38/0.57           sk_B)
% 0.38/0.57          | (zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.38/0.57         ((zip_tseitin_1 @ X24 @ X25 @ X26 @ X27)
% 0.38/0.57          | ~ (r2_hidden @ (k1_funct_1 @ X25 @ X24) @ X26))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A)
% 0.38/0.57          | (zip_tseitin_1 @ (sk_D_3 @ sk_C_2 @ X0 @ sk_A) @ sk_C_2 @ sk_B @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (zip_tseitin_1 @ (sk_D_3 @ sk_C_2 @ X0 @ sk_A) @ sk_C_2 @ X0 @ sk_A)
% 0.38/0.57          | (zip_tseitin_2 @ sk_C_2 @ X0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (((zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A)
% 0.38/0.57        | (zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain, ((zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.57         ((m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.38/0.57          | ~ (zip_tseitin_2 @ X28 @ X29 @ X30))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (($false)
% 0.38/0.57         <= (~
% 0.38/0.57             ((m1_subset_1 @ sk_C_2 @ 
% 0.38/0.57               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.57      inference('demod', [status(thm)], ['1', '46'])).
% 0.38/0.57  thf('48', plain, ((v1_funct_1 @ sk_C_2)),
% 0.38/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('49', plain, ((~ (v1_funct_1 @ sk_C_2)) <= (~ ((v1_funct_1 @ sk_C_2)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('50', plain, (((v1_funct_1 @ sk_C_2))),
% 0.38/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.57  thf('51', plain, ((zip_tseitin_2 @ sk_C_2 @ sk_B @ sk_A)),
% 0.38/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.38/0.57         ((v1_funct_2 @ X28 @ X30 @ X29) | ~ (zip_tseitin_2 @ X28 @ X29 @ X30))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.38/0.57  thf('53', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.38/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      ((~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))
% 0.38/0.57         <= (~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('55', plain, (((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      (~ ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.38/0.57       ~ ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)) | ~ ((v1_funct_1 @ sk_C_2))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      (~ ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['50', '55', '56'])).
% 0.38/0.57  thf('58', plain, ($false),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['47', '57'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

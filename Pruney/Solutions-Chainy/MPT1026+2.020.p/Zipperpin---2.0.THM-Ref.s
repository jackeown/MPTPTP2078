%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GzDDZNarXD

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:55 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 545 expanded)
%              Number of leaves         :   33 ( 169 expanded)
%              Depth                    :   16
%              Number of atoms          :  700 (6297 expanded)
%              Number of equality atoms :   18 ( 242 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_1 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_1 @ D @ C @ B @ A ) )
       => ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != X26 )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X27 @ X28 @ X26 ) @ X27 @ X28 @ X26 )
      | ( zip_tseitin_2 @ X27 @ X28 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( zip_tseitin_2 @ X27 @ X28 @ ( k1_relat_1 @ X27 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X27 @ X28 @ ( k1_relat_1 @ X27 ) ) @ X27 @ X28 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X5 @ X4 ) @ ( k2_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ( zip_tseitin_2 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r2_hidden @ sk_C_1 @ ( k1_funct_2 @ sk_A @ sk_B ) ),
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

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B )
        & ( ( k1_relat_1 @ E )
          = A )
        & ( D = E )
        & ( v1_funct_1 @ E )
        & ( v1_relat_1 @ E ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k1_funct_2 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i] :
              ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ( X15
       != ( k1_funct_2 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('11',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X13 @ X14 ) @ X16 @ X13 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_funct_2 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['9','11'])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8 = X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('15',plain,
    ( sk_C_1
    = ( sk_E_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( zip_tseitin_2 @ sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','20'])).

thf('22',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('24',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v1_funct_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['12','15'])).

thf('29',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ X6 )
        = X9 )
      | ~ ( zip_tseitin_0 @ X6 @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('30',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','24','27','30','31'])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_1 @ X19 @ X20 @ X21 @ X22 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X20 @ X19 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A )
      | ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ( zip_tseitin_2 @ X27 @ X28 @ ( k1_relat_1 @ X27 ) )
      | ~ ( zip_tseitin_1 @ ( sk_D_1 @ X27 @ X28 @ ( k1_relat_1 @ X27 ) ) @ X27 @ X28 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_C_1 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( sk_D_1 @ sk_C_1 @ X0 @ sk_A ) @ sk_C_1 @ X0 @ sk_A )
      | ( zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A )
    | ( zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( zip_tseitin_2 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( $false
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['25','26'])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['44'])).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_funct_2 @ X23 @ X25 @ X24 )
      | ~ ( zip_tseitin_2 @ X23 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,(
    ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['51','56','57'])).

thf('59',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['48','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GzDDZNarXD
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:54:39 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 115 iterations in 0.097s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.38/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.38/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.56  thf(t121_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.56       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.38/0.56          ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t121_funct_2])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      ((~ (v1_funct_1 @ sk_C_1)
% 0.38/0.56        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.38/0.56        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.38/0.56         <= (~
% 0.38/0.56             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf(t5_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.38/0.56       ( ( ( ![D:$i]:
% 0.38/0.56             ( ( r2_hidden @ D @ A ) =>
% 0.38/0.56               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.38/0.56           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.38/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.56           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_1, axiom,
% 0.38/0.56    (![D:$i,C:$i,B:$i,A:$i]:
% 0.38/0.56     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.38/0.56       ( zip_tseitin_1 @ D @ C @ B @ A ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.56         ((zip_tseitin_1 @ X19 @ X20 @ X21 @ X22) | (r2_hidden @ X19 @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.56  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_3, axiom,
% 0.38/0.56    (![C:$i,B:$i,A:$i]:
% 0.38/0.56     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.38/0.56       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_5, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.56       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.38/0.56           ( ![D:$i]: ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) =>
% 0.38/0.56         ( zip_tseitin_2 @ C @ B @ A ) ) ))).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.56         (((k1_relat_1 @ X27) != (X26))
% 0.38/0.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X27 @ X28 @ X26) @ X27 @ X28 @ X26)
% 0.38/0.56          | (zip_tseitin_2 @ X27 @ X28 @ X26)
% 0.38/0.56          | ~ (v1_funct_1 @ X27)
% 0.38/0.56          | ~ (v1_relat_1 @ X27))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X27 : $i, X28 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X27)
% 0.38/0.56          | ~ (v1_funct_1 @ X27)
% 0.38/0.56          | (zip_tseitin_2 @ X27 @ X28 @ (k1_relat_1 @ X27))
% 0.38/0.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X27 @ X28 @ (k1_relat_1 @ X27)) @ 
% 0.38/0.56               X27 @ X28 @ (k1_relat_1 @ X27)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_D_1 @ X0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.38/0.56           (k1_relat_1 @ X0))
% 0.38/0.56          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '4'])).
% 0.38/0.56  thf(t12_funct_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.38/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.38/0.56         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      (![X4 : $i, X5 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X4 @ (k1_relat_1 @ X5))
% 0.38/0.56          | (r2_hidden @ (k1_funct_1 @ X5 @ X4) @ (k2_relat_1 @ X5))
% 0.38/0.56          | ~ (v1_funct_1 @ X5)
% 0.38/0.56          | ~ (v1_relat_1 @ X5))),
% 0.38/0.56      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (k1_funct_1 @ X0 @ (sk_D_1 @ X0 @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.38/0.56             (k2_relat_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((r2_hidden @ 
% 0.38/0.56           (k1_funct_1 @ X0 @ (sk_D_1 @ X0 @ X1 @ (k1_relat_1 @ X0))) @ 
% 0.38/0.56           (k2_relat_1 @ X0))
% 0.38/0.56          | (zip_tseitin_2 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['7'])).
% 0.38/0.56  thf('9', plain, ((r2_hidden @ sk_C_1 @ (k1_funct_2 @ sk_A @ sk_B))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(d2_funct_2, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ?[E:$i]:
% 0.38/0.56             ( ( v1_relat_1 @ E ) & ( v1_funct_1 @ E ) & ( ( D ) = ( E ) ) & 
% 0.38/0.56               ( ( k1_relat_1 @ E ) = ( A ) ) & 
% 0.38/0.56               ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_7, axiom,
% 0.38/0.56    (![E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.56     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.38/0.56       ( ( r1_tarski @ ( k2_relat_1 @ E ) @ B ) & 
% 0.38/0.56         ( ( k1_relat_1 @ E ) = ( A ) ) & ( ( D ) = ( E ) ) & 
% 0.38/0.56         ( v1_funct_1 @ E ) & ( v1_relat_1 @ E ) ) ))).
% 0.38/0.56  thf(zf_stmt_8, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k1_funct_2 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X16 @ X15)
% 0.38/0.56          | (zip_tseitin_0 @ (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.38/0.56          | ((X15) != (k1_funct_2 @ X14 @ X13)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.38/0.56         ((zip_tseitin_0 @ (sk_E_1 @ X16 @ X13 @ X14) @ X16 @ X13 @ X14)
% 0.38/0.56          | ~ (r2_hidden @ X16 @ (k1_funct_2 @ X14 @ X13)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      ((zip_tseitin_0 @ (sk_E_1 @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('sup-', [status(thm)], ['9', '11'])).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         (((X8) = (X6)) | ~ (zip_tseitin_0 @ X6 @ X8 @ X7 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.56  thf('15', plain, (((sk_C_1) = (sk_E_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.56  thf('16', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         ((r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.38/0.56          | ~ (zip_tseitin_0 @ X6 @ X8 @ X7 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.56  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.38/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.56  thf(d3_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.56          | (r2_hidden @ X0 @ X2)
% 0.38/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ sk_C_1)
% 0.38/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.56          | (zip_tseitin_2 @ sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (k1_funct_1 @ sk_C_1 @ 
% 0.38/0.56              (sk_D_1 @ sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_1))) @ 
% 0.38/0.56             sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['8', '20'])).
% 0.38/0.56  thf('22', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         ((v1_relat_1 @ X6) | ~ (zip_tseitin_0 @ X6 @ X8 @ X7 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.56  thf('24', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('25', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         ((v1_funct_1 @ X6) | ~ (zip_tseitin_0 @ X6 @ X8 @ X7 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.56  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain, ((zip_tseitin_0 @ sk_C_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('demod', [status(thm)], ['12', '15'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.38/0.56         (((k1_relat_1 @ X6) = (X9)) | ~ (zip_tseitin_0 @ X6 @ X8 @ X7 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.38/0.56  thf('30', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('31', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A)
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (k1_funct_1 @ sk_C_1 @ (sk_D_1 @ sk_C_1 @ X0 @ sk_A)) @ sk_B))),
% 0.38/0.56      inference('demod', [status(thm)], ['21', '24', '27', '30', '31'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.56         ((zip_tseitin_1 @ X19 @ X20 @ X21 @ X22)
% 0.38/0.56          | ~ (r2_hidden @ (k1_funct_1 @ X20 @ X19) @ X21))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A)
% 0.38/0.56          | (zip_tseitin_1 @ (sk_D_1 @ sk_C_1 @ X0 @ sk_A) @ sk_C_1 @ sk_B @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf('35', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X27 : $i, X28 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X27)
% 0.38/0.56          | ~ (v1_funct_1 @ X27)
% 0.38/0.56          | (zip_tseitin_2 @ X27 @ X28 @ (k1_relat_1 @ X27))
% 0.38/0.56          | ~ (zip_tseitin_1 @ (sk_D_1 @ X27 @ X28 @ (k1_relat_1 @ X27)) @ 
% 0.38/0.56               X27 @ X28 @ (k1_relat_1 @ X27)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (zip_tseitin_1 @ (sk_D_1 @ sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_1)) @ 
% 0.38/0.56             sk_C_1 @ X0 @ sk_A)
% 0.38/0.56          | (zip_tseitin_2 @ sk_C_1 @ X0 @ (k1_relat_1 @ sk_C_1))
% 0.38/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.38/0.56          | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('39', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (zip_tseitin_1 @ (sk_D_1 @ sk_C_1 @ X0 @ sk_A) @ sk_C_1 @ X0 @ sk_A)
% 0.38/0.56          | (zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A)
% 0.38/0.56          | ~ (v1_relat_1 @ sk_C_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.38/0.56  thf('42', plain, ((v1_relat_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (zip_tseitin_1 @ (sk_D_1 @ sk_C_1 @ X0 @ sk_A) @ sk_C_1 @ X0 @ sk_A)
% 0.38/0.56          | (zip_tseitin_2 @ sk_C_1 @ X0 @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (((zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A)
% 0.38/0.56        | (zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['34', '43'])).
% 0.38/0.56  thf('45', plain, ((zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.56         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.38/0.56          | ~ (zip_tseitin_2 @ X23 @ X24 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (($false)
% 0.38/0.56         <= (~
% 0.38/0.56             ((m1_subset_1 @ sk_C_1 @ 
% 0.38/0.56               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.38/0.56      inference('demod', [status(thm)], ['1', '47'])).
% 0.38/0.56  thf('49', plain, ((v1_funct_1 @ sk_C_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('50', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('51', plain, (((v1_funct_1 @ sk_C_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.56  thf('52', plain, ((zip_tseitin_2 @ sk_C_1 @ sk_B @ sk_A)),
% 0.38/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.56         ((v1_funct_2 @ X23 @ X25 @ X24) | ~ (zip_tseitin_2 @ X23 @ X24 @ X25))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.56  thf('54', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.38/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.38/0.56         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('56', plain, (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.38/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.38/0.56       ~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)) | ~ ((v1_funct_1 @ sk_C_1))),
% 0.38/0.56      inference('split', [status(esa)], ['0'])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      (~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['51', '56', '57'])).
% 0.38/0.56  thf('59', plain, ($false),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['48', '58'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

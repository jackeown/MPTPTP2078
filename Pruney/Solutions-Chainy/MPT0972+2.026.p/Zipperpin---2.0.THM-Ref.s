%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FgSghgSvvn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:36 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :  208 (1151 expanded)
%              Number of leaves         :   39 ( 358 expanded)
%              Depth                    :   25
%              Number of atoms          : 1550 (14896 expanded)
%              Number of equality atoms :  128 ( 764 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t18_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( r2_hidden @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( r2_hidden @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('19',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_2 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_2 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('37',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_D = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('60',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('61',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['62','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['58','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['43','82'])).

thf('84',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','14'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('94',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('101',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('104',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['98','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('108',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('110',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['106','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('116',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_D = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['59','61'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('124',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['101','104'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['122','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['121','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['114','134'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('136',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X17 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('139',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('140',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['114','134'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['137','140','141','142'])).

thf('144',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('147',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['144','147','148'])).

thf('150',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X36: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X36 )
        = ( k1_funct_1 @ sk_D @ X36 ) )
      | ~ ( r2_hidden @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['152'])).

thf('154',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( X17 = X16 )
      | ( ( k1_funct_1 @ X17 @ ( sk_C_1 @ X16 @ X17 ) )
       != ( k1_funct_1 @ X16 @ ( sk_C_1 @ X16 @ X17 ) ) )
      | ( ( k1_relat_1 @ X17 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('155',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['138','139'])).

thf('157',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['114','134'])).

thf('159',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['83','90'])).

thf('160',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['145','146'])).

thf('162',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['155','156','157','158','159','160','161'])).

thf('163',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('166',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    $false ),
    inference(demod,[status(thm)],['0','163','166'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FgSghgSvvn
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:22:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.97/4.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.97/4.17  % Solved by: fo/fo7.sh
% 3.97/4.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.97/4.17  % done 3942 iterations in 3.720s
% 3.97/4.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.97/4.17  % SZS output start Refutation
% 3.97/4.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.97/4.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.97/4.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.97/4.17  thf(sk_A_type, type, sk_A: $i).
% 3.97/4.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.97/4.17  thf(sk_B_type, type, sk_B: $i).
% 3.97/4.17  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.97/4.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.97/4.17  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.97/4.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.97/4.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.97/4.17  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.97/4.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.97/4.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.97/4.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.97/4.17  thf(sk_D_type, type, sk_D: $i).
% 3.97/4.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.97/4.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.97/4.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.97/4.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.97/4.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.97/4.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.97/4.17  thf(t18_funct_2, conjecture,
% 3.97/4.17    (![A:$i,B:$i,C:$i]:
% 3.97/4.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.97/4.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.97/4.17       ( ![D:$i]:
% 3.97/4.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.97/4.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.97/4.17           ( ( ![E:$i]:
% 3.97/4.17               ( ( r2_hidden @ E @ A ) =>
% 3.97/4.17                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.97/4.17             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.97/4.17  thf(zf_stmt_0, negated_conjecture,
% 3.97/4.17    (~( ![A:$i,B:$i,C:$i]:
% 3.97/4.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.97/4.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.97/4.17          ( ![D:$i]:
% 3.97/4.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.97/4.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.97/4.17              ( ( ![E:$i]:
% 3.97/4.17                  ( ( r2_hidden @ E @ A ) =>
% 3.97/4.17                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.97/4.17                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.97/4.17    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 3.97/4.17  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf(d1_funct_2, axiom,
% 3.97/4.17    (![A:$i,B:$i,C:$i]:
% 3.97/4.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.97/4.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.97/4.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.97/4.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.97/4.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.97/4.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.97/4.17  thf(zf_stmt_1, axiom,
% 3.97/4.17    (![B:$i,A:$i]:
% 3.97/4.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.97/4.17       ( zip_tseitin_0 @ B @ A ) ))).
% 3.97/4.17  thf('1', plain,
% 3.97/4.17      (![X28 : $i, X29 : $i]:
% 3.97/4.17         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.97/4.17  thf(t113_zfmisc_1, axiom,
% 3.97/4.17    (![A:$i,B:$i]:
% 3.97/4.17     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.97/4.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.97/4.17  thf('2', plain,
% 3.97/4.17      (![X8 : $i, X9 : $i]:
% 3.97/4.17         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 3.97/4.17      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.97/4.17  thf('3', plain,
% 3.97/4.17      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.97/4.17      inference('simplify', [status(thm)], ['2'])).
% 3.97/4.17  thf('4', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.17         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.97/4.17      inference('sup+', [status(thm)], ['1', '3'])).
% 3.97/4.17  thf('5', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.97/4.17  thf(zf_stmt_3, axiom,
% 3.97/4.17    (![C:$i,B:$i,A:$i]:
% 3.97/4.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.97/4.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.97/4.17  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.97/4.17  thf(zf_stmt_5, axiom,
% 3.97/4.17    (![A:$i,B:$i,C:$i]:
% 3.97/4.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.97/4.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.97/4.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.97/4.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.97/4.17  thf('6', plain,
% 3.97/4.17      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.97/4.17         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.97/4.17          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.97/4.17          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.97/4.17  thf('7', plain,
% 3.97/4.17      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.17  thf('8', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.97/4.17          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['4', '7'])).
% 3.97/4.17  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('10', plain,
% 3.97/4.17      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.97/4.17         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 3.97/4.17          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 3.97/4.17          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.97/4.17  thf('11', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 3.97/4.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['9', '10'])).
% 3.97/4.17  thf('12', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf(redefinition_k1_relset_1, axiom,
% 3.97/4.17    (![A:$i,B:$i,C:$i]:
% 3.97/4.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.97/4.17  thf('13', plain,
% 3.97/4.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.97/4.17         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.97/4.17          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.97/4.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.97/4.17  thf('14', plain,
% 3.97/4.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.97/4.17      inference('sup-', [status(thm)], ['12', '13'])).
% 3.97/4.17  thf('15', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('demod', [status(thm)], ['11', '14'])).
% 3.97/4.17  thf('16', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((k2_zfmisc_1 @ X0 @ sk_B) = (k1_xboole_0))
% 3.97/4.17          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['8', '15'])).
% 3.97/4.17  thf(d3_tarski, axiom,
% 3.97/4.17    (![A:$i,B:$i]:
% 3.97/4.17     ( ( r1_tarski @ A @ B ) <=>
% 3.97/4.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.97/4.17  thf('17', plain,
% 3.97/4.17      (![X1 : $i, X3 : $i]:
% 3.97/4.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.97/4.17      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.17  thf(d10_xboole_0, axiom,
% 3.97/4.17    (![A:$i,B:$i]:
% 3.97/4.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.97/4.17  thf('18', plain,
% 3.97/4.17      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 3.97/4.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.97/4.17  thf('19', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 3.97/4.17      inference('simplify', [status(thm)], ['18'])).
% 3.97/4.17  thf(t3_subset, axiom,
% 3.97/4.17    (![A:$i,B:$i]:
% 3.97/4.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.97/4.17  thf('20', plain,
% 3.97/4.17      (![X10 : $i, X12 : $i]:
% 3.97/4.17         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 3.97/4.17      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.17  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['19', '20'])).
% 3.97/4.17  thf(t5_subset, axiom,
% 3.97/4.17    (![A:$i,B:$i,C:$i]:
% 3.97/4.17     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.97/4.17          ( v1_xboole_0 @ C ) ) ))).
% 3.97/4.17  thf('22', plain,
% 3.97/4.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.97/4.17         (~ (r2_hidden @ X13 @ X14)
% 3.97/4.17          | ~ (v1_xboole_0 @ X15)
% 3.97/4.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 3.97/4.17      inference('cnf', [status(esa)], [t5_subset])).
% 3.97/4.17  thf('23', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['21', '22'])).
% 3.97/4.17  thf('24', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['17', '23'])).
% 3.97/4.17  thf('25', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('26', plain,
% 3.97/4.17      (![X10 : $i, X11 : $i]:
% 3.97/4.17         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 3.97/4.17      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.17  thf('27', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 3.97/4.17      inference('sup-', [status(thm)], ['25', '26'])).
% 3.97/4.17  thf('28', plain,
% 3.97/4.17      (![X4 : $i, X6 : $i]:
% 3.97/4.17         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.97/4.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.97/4.17  thf('29', plain,
% 3.97/4.17      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_2)
% 3.97/4.17        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['27', '28'])).
% 3.97/4.17  thf('30', plain,
% 3.97/4.17      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.97/4.17        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['24', '29'])).
% 3.97/4.17  thf('31', plain,
% 3.97/4.17      ((~ (v1_xboole_0 @ k1_xboole_0)
% 3.97/4.17        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.97/4.17        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['16', '30'])).
% 3.97/4.17  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.97/4.17  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.97/4.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.97/4.17  thf('33', plain,
% 3.97/4.17      ((((sk_A) = (k1_relat_1 @ sk_D))
% 3.97/4.17        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_2)))),
% 3.97/4.17      inference('demod', [status(thm)], ['31', '32'])).
% 3.97/4.17  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.97/4.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.97/4.17  thf('35', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['17', '23'])).
% 3.97/4.17  thf('36', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['17', '23'])).
% 3.97/4.17  thf('37', plain,
% 3.97/4.17      (![X4 : $i, X6 : $i]:
% 3.97/4.17         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 3.97/4.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.97/4.17  thf('38', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.17  thf('39', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['35', '38'])).
% 3.97/4.17  thf('40', plain,
% 3.97/4.17      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['34', '39'])).
% 3.97/4.17  thf('41', plain,
% 3.97/4.17      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 3.97/4.17      inference('simplify', [status(thm)], ['2'])).
% 3.97/4.17  thf('42', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup+', [status(thm)], ['40', '41'])).
% 3.97/4.17  thf('43', plain,
% 3.97/4.17      ((((sk_C_2) = (k1_xboole_0))
% 3.97/4.17        | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.97/4.17        | ~ (v1_xboole_0 @ sk_B))),
% 3.97/4.17      inference('sup+', [status(thm)], ['33', '42'])).
% 3.97/4.17  thf('44', plain,
% 3.97/4.17      (![X1 : $i, X3 : $i]:
% 3.97/4.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.97/4.17      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.17  thf('45', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.17         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.97/4.17      inference('sup+', [status(thm)], ['1', '3'])).
% 3.97/4.17  thf('46', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('47', plain,
% 3.97/4.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.97/4.17         (~ (r2_hidden @ X13 @ X14)
% 3.97/4.17          | ~ (v1_xboole_0 @ X15)
% 3.97/4.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 3.97/4.17      inference('cnf', [status(esa)], [t5_subset])).
% 3.97/4.17  thf('48', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.97/4.17          | ~ (r2_hidden @ X0 @ sk_D))),
% 3.97/4.17      inference('sup-', [status(thm)], ['46', '47'])).
% 3.97/4.17  thf('49', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.97/4.17          | (zip_tseitin_0 @ sk_B @ X1)
% 3.97/4.17          | ~ (r2_hidden @ X0 @ sk_D))),
% 3.97/4.17      inference('sup-', [status(thm)], ['45', '48'])).
% 3.97/4.17  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.97/4.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.97/4.17  thf('51', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         ((zip_tseitin_0 @ sk_B @ X1) | ~ (r2_hidden @ X0 @ sk_D))),
% 3.97/4.17      inference('demod', [status(thm)], ['49', '50'])).
% 3.97/4.17  thf('52', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_D @ X0) | (zip_tseitin_0 @ sk_B @ X1))),
% 3.97/4.17      inference('sup-', [status(thm)], ['44', '51'])).
% 3.97/4.17  thf('53', plain,
% 3.97/4.17      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.17  thf('54', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_D @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['52', '53'])).
% 3.97/4.17  thf('55', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('demod', [status(thm)], ['11', '14'])).
% 3.97/4.17  thf('56', plain,
% 3.97/4.17      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['54', '55'])).
% 3.97/4.17  thf('57', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.17  thf('58', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((sk_A) = (k1_relat_1 @ sk_D))
% 3.97/4.17          | ((sk_D) = (X0))
% 3.97/4.17          | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['56', '57'])).
% 3.97/4.17  thf('59', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf(redefinition_r2_relset_1, axiom,
% 3.97/4.17    (![A:$i,B:$i,C:$i,D:$i]:
% 3.97/4.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.97/4.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.97/4.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.97/4.17  thf('60', plain,
% 3.97/4.17      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.97/4.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.97/4.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.97/4.17          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 3.97/4.17          | ((X24) != (X27)))),
% 3.97/4.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.97/4.17  thf('61', plain,
% 3.97/4.17      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.97/4.17         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 3.97/4.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.97/4.17      inference('simplify', [status(thm)], ['60'])).
% 3.97/4.17  thf('62', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 3.97/4.17      inference('sup-', [status(thm)], ['59', '61'])).
% 3.97/4.17  thf('63', plain,
% 3.97/4.17      (![X1 : $i, X3 : $i]:
% 3.97/4.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 3.97/4.17      inference('cnf', [status(esa)], [d3_tarski])).
% 3.97/4.17  thf('64', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.17         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 3.97/4.17      inference('sup+', [status(thm)], ['1', '3'])).
% 3.97/4.17  thf('65', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('66', plain,
% 3.97/4.17      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.97/4.17         (~ (r2_hidden @ X13 @ X14)
% 3.97/4.17          | ~ (v1_xboole_0 @ X15)
% 3.97/4.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 3.97/4.17      inference('cnf', [status(esa)], [t5_subset])).
% 3.97/4.17  thf('67', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 3.97/4.17          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.97/4.17      inference('sup-', [status(thm)], ['65', '66'])).
% 3.97/4.17  thf('68', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.97/4.17          | (zip_tseitin_0 @ sk_B @ X1)
% 3.97/4.17          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.97/4.17      inference('sup-', [status(thm)], ['64', '67'])).
% 3.97/4.17  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.97/4.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.97/4.17  thf('70', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         ((zip_tseitin_0 @ sk_B @ X1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 3.97/4.17      inference('demod', [status(thm)], ['68', '69'])).
% 3.97/4.17  thf('71', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_0 @ sk_B @ X1))),
% 3.97/4.17      inference('sup-', [status(thm)], ['63', '70'])).
% 3.97/4.17  thf('72', plain,
% 3.97/4.17      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.17  thf('73', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['71', '72'])).
% 3.97/4.17  thf('74', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('demod', [status(thm)], ['11', '14'])).
% 3.97/4.17  thf('75', plain,
% 3.97/4.17      (![X0 : $i]: ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['73', '74'])).
% 3.97/4.17  thf('76', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.17  thf('77', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((sk_A) = (k1_relat_1 @ sk_D))
% 3.97/4.17          | ((sk_C_2) = (X0))
% 3.97/4.17          | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['75', '76'])).
% 3.97/4.17  thf('78', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('79', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 3.97/4.17          | ~ (v1_xboole_0 @ X0)
% 3.97/4.17          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['77', '78'])).
% 3.97/4.17  thf('80', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ sk_D))),
% 3.97/4.17      inference('sup-', [status(thm)], ['62', '79'])).
% 3.97/4.17  thf('81', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X0)
% 3.97/4.17          | ~ (v1_xboole_0 @ X0)
% 3.97/4.17          | ((sk_A) = (k1_relat_1 @ sk_D))
% 3.97/4.17          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['58', '80'])).
% 3.97/4.17  thf('82', plain,
% 3.97/4.17      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('simplify', [status(thm)], ['81'])).
% 3.97/4.17  thf('83', plain, ((~ (v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('clc', [status(thm)], ['43', '82'])).
% 3.97/4.17  thf('84', plain,
% 3.97/4.17      (![X28 : $i, X29 : $i]:
% 3.97/4.17         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.97/4.17  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.97/4.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.97/4.17  thf('86', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.97/4.17      inference('sup+', [status(thm)], ['84', '85'])).
% 3.97/4.17  thf('87', plain,
% 3.97/4.17      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['5', '6'])).
% 3.97/4.17  thf('88', plain,
% 3.97/4.17      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['86', '87'])).
% 3.97/4.17  thf('89', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('demod', [status(thm)], ['11', '14'])).
% 3.97/4.17  thf('90', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['88', '89'])).
% 3.97/4.17  thf('91', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.97/4.17      inference('clc', [status(thm)], ['83', '90'])).
% 3.97/4.17  thf('92', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.97/4.17      inference('sup+', [status(thm)], ['84', '85'])).
% 3.97/4.17  thf('93', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['17', '23'])).
% 3.97/4.17  thf('94', plain,
% 3.97/4.17      (![X10 : $i, X12 : $i]:
% 3.97/4.17         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 3.97/4.17      inference('cnf', [status(esa)], [t3_subset])).
% 3.97/4.17  thf('95', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['93', '94'])).
% 3.97/4.17  thf('96', plain,
% 3.97/4.17      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.97/4.17         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.97/4.17          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.97/4.17          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.97/4.17  thf('97', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X2)
% 3.97/4.17          | (zip_tseitin_1 @ X2 @ X0 @ X1)
% 3.97/4.17          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.97/4.17      inference('sup-', [status(thm)], ['95', '96'])).
% 3.97/4.17  thf('98', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.97/4.17         ((v1_xboole_0 @ X1)
% 3.97/4.17          | (zip_tseitin_1 @ X2 @ X1 @ X0)
% 3.97/4.17          | ~ (v1_xboole_0 @ X2))),
% 3.97/4.17      inference('sup-', [status(thm)], ['92', '97'])).
% 3.97/4.17  thf('99', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('100', plain,
% 3.97/4.17      (![X30 : $i, X31 : $i, X32 : $i]:
% 3.97/4.17         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 3.97/4.17          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 3.97/4.17          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.97/4.17  thf('101', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['99', '100'])).
% 3.97/4.17  thf('102', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('103', plain,
% 3.97/4.17      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.97/4.17         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 3.97/4.17          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.97/4.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.97/4.17  thf('104', plain,
% 3.97/4.17      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.97/4.17      inference('sup-', [status(thm)], ['102', '103'])).
% 3.97/4.17  thf('105', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('demod', [status(thm)], ['101', '104'])).
% 3.97/4.17  thf('106', plain,
% 3.97/4.17      ((~ (v1_xboole_0 @ sk_C_2)
% 3.97/4.17        | (v1_xboole_0 @ sk_B)
% 3.97/4.17        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['98', '105'])).
% 3.97/4.17  thf('107', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.97/4.17      inference('sup+', [status(thm)], ['84', '85'])).
% 3.97/4.17  thf('108', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('109', plain,
% 3.97/4.17      (![X33 : $i, X34 : $i, X35 : $i]:
% 3.97/4.17         (~ (zip_tseitin_0 @ X33 @ X34)
% 3.97/4.17          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 3.97/4.17          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.97/4.17  thf('110', plain,
% 3.97/4.17      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['108', '109'])).
% 3.97/4.17  thf('111', plain,
% 3.97/4.17      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['107', '110'])).
% 3.97/4.17  thf('112', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('demod', [status(thm)], ['101', '104'])).
% 3.97/4.17  thf('113', plain,
% 3.97/4.17      (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['111', '112'])).
% 3.97/4.17  thf('114', plain,
% 3.97/4.17      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | (v1_xboole_0 @ sk_B))),
% 3.97/4.17      inference('clc', [status(thm)], ['106', '113'])).
% 3.97/4.17  thf('115', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_D @ X0) | (zip_tseitin_0 @ sk_B @ X1))),
% 3.97/4.17      inference('sup-', [status(thm)], ['44', '51'])).
% 3.97/4.17  thf('116', plain,
% 3.97/4.17      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['108', '109'])).
% 3.97/4.17  thf('117', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_D @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['115', '116'])).
% 3.97/4.17  thf('118', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('demod', [status(thm)], ['101', '104'])).
% 3.97/4.17  thf('119', plain,
% 3.97/4.17      (![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['117', '118'])).
% 3.97/4.17  thf('120', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.17  thf('121', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.97/4.17          | ((sk_D) = (X0))
% 3.97/4.17          | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['119', '120'])).
% 3.97/4.17  thf('122', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_D @ sk_D)),
% 3.97/4.17      inference('sup-', [status(thm)], ['59', '61'])).
% 3.97/4.17  thf('123', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_0 @ sk_B @ X1))),
% 3.97/4.17      inference('sup-', [status(thm)], ['63', '70'])).
% 3.97/4.17  thf('124', plain,
% 3.97/4.17      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['108', '109'])).
% 3.97/4.17  thf('125', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_C_2 @ X0) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['123', '124'])).
% 3.97/4.17  thf('126', plain,
% 3.97/4.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 3.97/4.17        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('demod', [status(thm)], ['101', '104'])).
% 3.97/4.17  thf('127', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         ((r1_tarski @ sk_C_2 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['125', '126'])).
% 3.97/4.17  thf('128', plain,
% 3.97/4.17      (![X0 : $i, X1 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['36', '37'])).
% 3.97/4.17  thf('129', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.97/4.17          | ((sk_C_2) = (X0))
% 3.97/4.17          | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['127', '128'])).
% 3.97/4.17  thf('130', plain, (~ (r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('131', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (~ (r2_relset_1 @ sk_A @ sk_B @ X0 @ sk_D)
% 3.97/4.17          | ~ (v1_xboole_0 @ X0)
% 3.97/4.17          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['129', '130'])).
% 3.97/4.17  thf('132', plain,
% 3.97/4.17      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_D))),
% 3.97/4.17      inference('sup-', [status(thm)], ['122', '131'])).
% 3.97/4.17  thf('133', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (~ (v1_xboole_0 @ X0)
% 3.97/4.17          | ~ (v1_xboole_0 @ X0)
% 3.97/4.17          | ((sk_A) = (k1_relat_1 @ sk_C_2))
% 3.97/4.17          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.97/4.17      inference('sup-', [status(thm)], ['121', '132'])).
% 3.97/4.17  thf('134', plain,
% 3.97/4.17      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ X0))),
% 3.97/4.17      inference('simplify', [status(thm)], ['133'])).
% 3.97/4.17  thf('135', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.97/4.17      inference('clc', [status(thm)], ['114', '134'])).
% 3.97/4.17  thf(t9_funct_1, axiom,
% 3.97/4.17    (![A:$i]:
% 3.97/4.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.97/4.17       ( ![B:$i]:
% 3.97/4.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.97/4.17           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.97/4.17               ( ![C:$i]:
% 3.97/4.17                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.97/4.17                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.97/4.17             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.97/4.17  thf('136', plain,
% 3.97/4.17      (![X16 : $i, X17 : $i]:
% 3.97/4.17         (~ (v1_relat_1 @ X16)
% 3.97/4.17          | ~ (v1_funct_1 @ X16)
% 3.97/4.17          | ((X17) = (X16))
% 3.97/4.17          | (r2_hidden @ (sk_C_1 @ X16 @ X17) @ (k1_relat_1 @ X17))
% 3.97/4.17          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 3.97/4.17          | ~ (v1_funct_1 @ X17)
% 3.97/4.17          | ~ (v1_relat_1 @ X17))),
% 3.97/4.17      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.97/4.17  thf('137', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((sk_A) != (k1_relat_1 @ X0))
% 3.97/4.17          | ~ (v1_relat_1 @ sk_C_2)
% 3.97/4.17          | ~ (v1_funct_1 @ sk_C_2)
% 3.97/4.17          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.97/4.17          | ((sk_C_2) = (X0))
% 3.97/4.17          | ~ (v1_funct_1 @ X0)
% 3.97/4.17          | ~ (v1_relat_1 @ X0))),
% 3.97/4.17      inference('sup-', [status(thm)], ['135', '136'])).
% 3.97/4.17  thf('138', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf(cc1_relset_1, axiom,
% 3.97/4.17    (![A:$i,B:$i,C:$i]:
% 3.97/4.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.97/4.17       ( v1_relat_1 @ C ) ))).
% 3.97/4.17  thf('139', plain,
% 3.97/4.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.97/4.17         ((v1_relat_1 @ X18)
% 3.97/4.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.97/4.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.97/4.17  thf('140', plain, ((v1_relat_1 @ sk_C_2)),
% 3.97/4.17      inference('sup-', [status(thm)], ['138', '139'])).
% 3.97/4.17  thf('141', plain, ((v1_funct_1 @ sk_C_2)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('142', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.97/4.17      inference('clc', [status(thm)], ['114', '134'])).
% 3.97/4.17  thf('143', plain,
% 3.97/4.17      (![X0 : $i]:
% 3.97/4.17         (((sk_A) != (k1_relat_1 @ X0))
% 3.97/4.17          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.97/4.17          | ((sk_C_2) = (X0))
% 3.97/4.17          | ~ (v1_funct_1 @ X0)
% 3.97/4.17          | ~ (v1_relat_1 @ X0))),
% 3.97/4.17      inference('demod', [status(thm)], ['137', '140', '141', '142'])).
% 3.97/4.17  thf('144', plain,
% 3.97/4.17      ((((sk_A) != (sk_A))
% 3.97/4.17        | ~ (v1_relat_1 @ sk_D)
% 3.97/4.17        | ~ (v1_funct_1 @ sk_D)
% 3.97/4.17        | ((sk_C_2) = (sk_D))
% 3.97/4.17        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.97/4.17      inference('sup-', [status(thm)], ['91', '143'])).
% 3.97/4.17  thf('145', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('146', plain,
% 3.97/4.17      (![X18 : $i, X19 : $i, X20 : $i]:
% 3.97/4.17         ((v1_relat_1 @ X18)
% 3.97/4.17          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 3.97/4.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.97/4.17  thf('147', plain, ((v1_relat_1 @ sk_D)),
% 3.97/4.17      inference('sup-', [status(thm)], ['145', '146'])).
% 3.97/4.17  thf('148', plain, ((v1_funct_1 @ sk_D)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('149', plain,
% 3.97/4.17      ((((sk_A) != (sk_A))
% 3.97/4.17        | ((sk_C_2) = (sk_D))
% 3.97/4.17        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.97/4.17      inference('demod', [status(thm)], ['144', '147', '148'])).
% 3.97/4.17  thf('150', plain,
% 3.97/4.17      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.97/4.17      inference('simplify', [status(thm)], ['149'])).
% 3.97/4.17  thf('151', plain,
% 3.97/4.17      (![X36 : $i]:
% 3.97/4.17         (((k1_funct_1 @ sk_C_2 @ X36) = (k1_funct_1 @ sk_D @ X36))
% 3.97/4.17          | ~ (r2_hidden @ X36 @ sk_A))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('152', plain,
% 3.97/4.17      ((((sk_C_2) = (sk_D))
% 3.97/4.17        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.97/4.17            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.97/4.17      inference('sup-', [status(thm)], ['150', '151'])).
% 3.97/4.17  thf('153', plain,
% 3.97/4.17      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.97/4.17         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.97/4.17      inference('condensation', [status(thm)], ['152'])).
% 3.97/4.17  thf('154', plain,
% 3.97/4.17      (![X16 : $i, X17 : $i]:
% 3.97/4.17         (~ (v1_relat_1 @ X16)
% 3.97/4.17          | ~ (v1_funct_1 @ X16)
% 3.97/4.17          | ((X17) = (X16))
% 3.97/4.17          | ((k1_funct_1 @ X17 @ (sk_C_1 @ X16 @ X17))
% 3.97/4.17              != (k1_funct_1 @ X16 @ (sk_C_1 @ X16 @ X17)))
% 3.97/4.17          | ((k1_relat_1 @ X17) != (k1_relat_1 @ X16))
% 3.97/4.17          | ~ (v1_funct_1 @ X17)
% 3.97/4.17          | ~ (v1_relat_1 @ X17))),
% 3.97/4.17      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.97/4.17  thf('155', plain,
% 3.97/4.17      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.97/4.17          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.97/4.17        | ~ (v1_relat_1 @ sk_C_2)
% 3.97/4.17        | ~ (v1_funct_1 @ sk_C_2)
% 3.97/4.17        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.97/4.17        | ((sk_C_2) = (sk_D))
% 3.97/4.17        | ~ (v1_funct_1 @ sk_D)
% 3.97/4.17        | ~ (v1_relat_1 @ sk_D))),
% 3.97/4.17      inference('sup-', [status(thm)], ['153', '154'])).
% 3.97/4.17  thf('156', plain, ((v1_relat_1 @ sk_C_2)),
% 3.97/4.17      inference('sup-', [status(thm)], ['138', '139'])).
% 3.97/4.17  thf('157', plain, ((v1_funct_1 @ sk_C_2)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('158', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.97/4.17      inference('clc', [status(thm)], ['114', '134'])).
% 3.97/4.17  thf('159', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.97/4.17      inference('clc', [status(thm)], ['83', '90'])).
% 3.97/4.17  thf('160', plain, ((v1_funct_1 @ sk_D)),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('161', plain, ((v1_relat_1 @ sk_D)),
% 3.97/4.17      inference('sup-', [status(thm)], ['145', '146'])).
% 3.97/4.17  thf('162', plain,
% 3.97/4.17      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.97/4.17          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.97/4.17        | ((sk_A) != (sk_A))
% 3.97/4.17        | ((sk_C_2) = (sk_D)))),
% 3.97/4.17      inference('demod', [status(thm)],
% 3.97/4.17                ['155', '156', '157', '158', '159', '160', '161'])).
% 3.97/4.17  thf('163', plain, (((sk_C_2) = (sk_D))),
% 3.97/4.17      inference('simplify', [status(thm)], ['162'])).
% 3.97/4.17  thf('164', plain,
% 3.97/4.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.97/4.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.97/4.17  thf('165', plain,
% 3.97/4.17      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.97/4.17         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 3.97/4.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 3.97/4.17      inference('simplify', [status(thm)], ['60'])).
% 3.97/4.17  thf('166', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C_2 @ sk_C_2)),
% 3.97/4.17      inference('sup-', [status(thm)], ['164', '165'])).
% 3.97/4.17  thf('167', plain, ($false),
% 3.97/4.17      inference('demod', [status(thm)], ['0', '163', '166'])).
% 3.97/4.17  
% 3.97/4.17  % SZS output end Refutation
% 3.97/4.17  
% 4.01/4.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

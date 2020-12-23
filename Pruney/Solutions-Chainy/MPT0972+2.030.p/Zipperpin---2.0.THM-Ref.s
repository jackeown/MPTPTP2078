%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8g2gVc5OI6

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:37 EST 2020

% Result     : Theorem 5.91s
% Output     : Refutation 5.91s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 711 expanded)
%              Number of leaves         :   43 ( 235 expanded)
%              Depth                    :   29
%              Number of atoms          : 1113 (7536 expanded)
%              Number of equality atoms :   75 ( 381 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('31',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('39',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('46',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_relset_1 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('47',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','49'])).

thf('51',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['53','66'])).

thf('68',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','67'])).

thf('69',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['53','66'])).

thf('81',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['76','81'])).

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

thf('83',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('86',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('87',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['84','87','88','89'])).

thf('91',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('94',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['91','94','95'])).

thf('97',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X38: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X38 )
        = ( k1_funct_1 @ sk_D @ X38 ) )
      | ~ ( r2_hidden @ X38 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['99'])).

thf('101',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( ( k1_funct_1 @ X18 @ ( sk_C_1 @ X17 @ X18 ) )
       != ( k1_funct_1 @ X17 @ ( sk_C_1 @ X17 @ X18 ) ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('102',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('104',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('106',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','68'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['92','93'])).

thf('109',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','107','108'])).

thf('110',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('113',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['0','110','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8g2gVc5OI6
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:42:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.91/6.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.91/6.17  % Solved by: fo/fo7.sh
% 5.91/6.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.91/6.17  % done 5994 iterations in 5.715s
% 5.91/6.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.91/6.17  % SZS output start Refutation
% 5.91/6.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.91/6.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.91/6.17  thf(sk_A_type, type, sk_A: $i).
% 5.91/6.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.91/6.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.91/6.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.91/6.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.91/6.17  thf(sk_D_type, type, sk_D: $i).
% 5.91/6.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.91/6.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.91/6.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.91/6.17  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.91/6.17  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.91/6.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.91/6.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.91/6.17  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.91/6.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.91/6.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.91/6.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.91/6.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.91/6.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.91/6.17  thf(sk_C_2_type, type, sk_C_2: $i).
% 5.91/6.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.91/6.17  thf(sk_B_type, type, sk_B: $i > $i).
% 5.91/6.17  thf(t18_funct_2, conjecture,
% 5.91/6.17    (![A:$i,B:$i,C:$i]:
% 5.91/6.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.91/6.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.91/6.17       ( ![D:$i]:
% 5.91/6.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.91/6.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.91/6.17           ( ( ![E:$i]:
% 5.91/6.17               ( ( r2_hidden @ E @ A ) =>
% 5.91/6.17                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.91/6.17             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 5.91/6.17  thf(zf_stmt_0, negated_conjecture,
% 5.91/6.17    (~( ![A:$i,B:$i,C:$i]:
% 5.91/6.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.91/6.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.91/6.17          ( ![D:$i]:
% 5.91/6.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.91/6.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.91/6.17              ( ( ![E:$i]:
% 5.91/6.17                  ( ( r2_hidden @ E @ A ) =>
% 5.91/6.17                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.91/6.17                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 5.91/6.17    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 5.91/6.17  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf(d1_funct_2, axiom,
% 5.91/6.17    (![A:$i,B:$i,C:$i]:
% 5.91/6.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.17       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.91/6.17           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.91/6.17             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.91/6.17         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.91/6.17           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.91/6.17             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.91/6.17  thf(zf_stmt_1, axiom,
% 5.91/6.17    (![C:$i,B:$i,A:$i]:
% 5.91/6.17     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.91/6.17       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.91/6.17  thf('2', plain,
% 5.91/6.17      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.91/6.17         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 5.91/6.17          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 5.91/6.17          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.91/6.17  thf('3', plain,
% 5.91/6.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.91/6.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 5.91/6.17      inference('sup-', [status(thm)], ['1', '2'])).
% 5.91/6.17  thf('4', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf(redefinition_k1_relset_1, axiom,
% 5.91/6.17    (![A:$i,B:$i,C:$i]:
% 5.91/6.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.17       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.91/6.17  thf('5', plain,
% 5.91/6.17      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.91/6.17         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 5.91/6.17          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.91/6.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.91/6.17  thf('6', plain,
% 5.91/6.17      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 5.91/6.17      inference('sup-', [status(thm)], ['4', '5'])).
% 5.91/6.17  thf('7', plain,
% 5.91/6.17      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.91/6.17        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.91/6.17      inference('demod', [status(thm)], ['3', '6'])).
% 5.91/6.17  thf('8', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.91/6.17  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.91/6.17  thf(zf_stmt_4, axiom,
% 5.91/6.17    (![B:$i,A:$i]:
% 5.91/6.17     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.91/6.17       ( zip_tseitin_0 @ B @ A ) ))).
% 5.91/6.17  thf(zf_stmt_5, axiom,
% 5.91/6.17    (![A:$i,B:$i,C:$i]:
% 5.91/6.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.17       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.91/6.17         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.91/6.17           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.91/6.17             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.91/6.17  thf('9', plain,
% 5.91/6.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.91/6.17         (~ (zip_tseitin_0 @ X35 @ X36)
% 5.91/6.17          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 5.91/6.17          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.91/6.17  thf('10', plain,
% 5.91/6.17      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.91/6.17        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 5.91/6.17      inference('sup-', [status(thm)], ['8', '9'])).
% 5.91/6.17  thf('11', plain,
% 5.91/6.17      (![X30 : $i, X31 : $i]:
% 5.91/6.17         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.91/6.17  thf(t113_zfmisc_1, axiom,
% 5.91/6.17    (![A:$i,B:$i]:
% 5.91/6.17     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.91/6.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.91/6.17  thf('12', plain,
% 5.91/6.17      (![X9 : $i, X10 : $i]:
% 5.91/6.17         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 5.91/6.17      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.91/6.17  thf('13', plain,
% 5.91/6.17      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 5.91/6.17      inference('simplify', [status(thm)], ['12'])).
% 5.91/6.17  thf('14', plain,
% 5.91/6.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.91/6.17         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.91/6.17      inference('sup+', [status(thm)], ['11', '13'])).
% 5.91/6.17  thf(d1_xboole_0, axiom,
% 5.91/6.17    (![A:$i]:
% 5.91/6.17     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.91/6.17  thf('15', plain,
% 5.91/6.17      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.91/6.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.91/6.17  thf('16', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf(t3_subset, axiom,
% 5.91/6.17    (![A:$i,B:$i]:
% 5.91/6.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 5.91/6.17  thf('17', plain,
% 5.91/6.17      (![X11 : $i, X12 : $i]:
% 5.91/6.17         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.91/6.17      inference('cnf', [status(esa)], [t3_subset])).
% 5.91/6.17  thf('18', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 5.91/6.17      inference('sup-', [status(thm)], ['16', '17'])).
% 5.91/6.17  thf(d3_tarski, axiom,
% 5.91/6.17    (![A:$i,B:$i]:
% 5.91/6.17     ( ( r1_tarski @ A @ B ) <=>
% 5.91/6.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.91/6.17  thf('19', plain,
% 5.91/6.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.91/6.17         (~ (r2_hidden @ X3 @ X4)
% 5.91/6.17          | (r2_hidden @ X3 @ X5)
% 5.91/6.17          | ~ (r1_tarski @ X4 @ X5))),
% 5.91/6.17      inference('cnf', [status(esa)], [d3_tarski])).
% 5.91/6.17  thf('20', plain,
% 5.91/6.17      (![X0 : $i]:
% 5.91/6.17         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 5.91/6.17          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 5.91/6.17      inference('sup-', [status(thm)], ['18', '19'])).
% 5.91/6.17  thf('21', plain,
% 5.91/6.17      (((v1_xboole_0 @ sk_C_2)
% 5.91/6.17        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('sup-', [status(thm)], ['15', '20'])).
% 5.91/6.17  thf('22', plain,
% 5.91/6.17      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.91/6.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.91/6.17  thf('23', plain,
% 5.91/6.17      (((v1_xboole_0 @ sk_C_2)
% 5.91/6.17        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('sup-', [status(thm)], ['21', '22'])).
% 5.91/6.17  thf('24', plain,
% 5.91/6.17      (![X0 : $i]:
% 5.91/6.17         (~ (v1_xboole_0 @ k1_xboole_0)
% 5.91/6.17          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 5.91/6.17          | (v1_xboole_0 @ sk_C_2))),
% 5.91/6.17      inference('sup-', [status(thm)], ['14', '23'])).
% 5.91/6.17  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.91/6.17  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.91/6.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.91/6.17  thf('26', plain,
% 5.91/6.17      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_2))),
% 5.91/6.17      inference('demod', [status(thm)], ['24', '25'])).
% 5.91/6.17  thf(l13_xboole_0, axiom,
% 5.91/6.17    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 5.91/6.17  thf('27', plain,
% 5.91/6.17      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 5.91/6.17      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.91/6.17  thf('28', plain,
% 5.91/6.17      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 5.91/6.17      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.91/6.17  thf('29', plain,
% 5.91/6.17      (![X4 : $i, X6 : $i]:
% 5.91/6.17         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 5.91/6.17      inference('cnf', [status(esa)], [d3_tarski])).
% 5.91/6.17  thf('30', plain,
% 5.91/6.17      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 5.91/6.17      inference('simplify', [status(thm)], ['12'])).
% 5.91/6.17  thf(t29_relset_1, axiom,
% 5.91/6.17    (![A:$i]:
% 5.91/6.17     ( m1_subset_1 @
% 5.91/6.17       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 5.91/6.17  thf('31', plain,
% 5.91/6.17      (![X29 : $i]:
% 5.91/6.17         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 5.91/6.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 5.91/6.17      inference('cnf', [status(esa)], [t29_relset_1])).
% 5.91/6.17  thf('32', plain,
% 5.91/6.17      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 5.91/6.17      inference('sup+', [status(thm)], ['30', '31'])).
% 5.91/6.17  thf(t5_subset, axiom,
% 5.91/6.17    (![A:$i,B:$i,C:$i]:
% 5.91/6.17     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 5.91/6.17          ( v1_xboole_0 @ C ) ) ))).
% 5.91/6.17  thf('33', plain,
% 5.91/6.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 5.91/6.17         (~ (r2_hidden @ X14 @ X15)
% 5.91/6.17          | ~ (v1_xboole_0 @ X16)
% 5.91/6.17          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 5.91/6.17      inference('cnf', [status(esa)], [t5_subset])).
% 5.91/6.17  thf('34', plain,
% 5.91/6.17      (![X0 : $i]:
% 5.91/6.17         (~ (v1_xboole_0 @ k1_xboole_0)
% 5.91/6.17          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 5.91/6.17      inference('sup-', [status(thm)], ['32', '33'])).
% 5.91/6.17  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.91/6.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.91/6.17  thf('36', plain,
% 5.91/6.17      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 5.91/6.17      inference('demod', [status(thm)], ['34', '35'])).
% 5.91/6.17  thf('37', plain,
% 5.91/6.17      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.91/6.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.91/6.17  thf('38', plain,
% 5.91/6.17      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 5.91/6.17      inference('demod', [status(thm)], ['34', '35'])).
% 5.91/6.17  thf('39', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 5.91/6.17      inference('sup-', [status(thm)], ['37', '38'])).
% 5.91/6.17  thf('40', plain,
% 5.91/6.17      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 5.91/6.17      inference('cnf', [status(esa)], [l13_xboole_0])).
% 5.91/6.17  thf('41', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.91/6.17      inference('sup-', [status(thm)], ['39', '40'])).
% 5.91/6.17  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 5.91/6.17      inference('demod', [status(thm)], ['36', '41'])).
% 5.91/6.17  thf('43', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 5.91/6.17      inference('sup-', [status(thm)], ['29', '42'])).
% 5.91/6.17  thf('44', plain,
% 5.91/6.17      (![X11 : $i, X13 : $i]:
% 5.91/6.17         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 5.91/6.17      inference('cnf', [status(esa)], [t3_subset])).
% 5.91/6.17  thf('45', plain,
% 5.91/6.17      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 5.91/6.17      inference('sup-', [status(thm)], ['43', '44'])).
% 5.91/6.17  thf(redefinition_r2_relset_1, axiom,
% 5.91/6.17    (![A:$i,B:$i,C:$i,D:$i]:
% 5.91/6.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.91/6.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.91/6.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.91/6.17  thf('46', plain,
% 5.91/6.17      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 5.91/6.17         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.91/6.17          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 5.91/6.17          | (r2_relset_1 @ X26 @ X27 @ X25 @ X28)
% 5.91/6.17          | ((X25) != (X28)))),
% 5.91/6.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.91/6.17  thf('47', plain,
% 5.91/6.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.91/6.17         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 5.91/6.17          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.91/6.17      inference('simplify', [status(thm)], ['46'])).
% 5.91/6.17  thf('48', plain,
% 5.91/6.17      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.91/6.17      inference('sup-', [status(thm)], ['45', '47'])).
% 5.91/6.17  thf('49', plain,
% 5.91/6.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.91/6.17         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 5.91/6.17      inference('sup+', [status(thm)], ['28', '48'])).
% 5.91/6.17  thf('50', plain,
% 5.91/6.17      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.91/6.17         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 5.91/6.17          | ~ (v1_xboole_0 @ X0)
% 5.91/6.17          | ~ (v1_xboole_0 @ X1))),
% 5.91/6.17      inference('sup+', [status(thm)], ['27', '49'])).
% 5.91/6.17  thf('51', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('52', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 5.91/6.17      inference('sup-', [status(thm)], ['50', '51'])).
% 5.91/6.17  thf('53', plain,
% 5.91/6.17      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 5.91/6.17      inference('sup-', [status(thm)], ['26', '52'])).
% 5.91/6.17  thf('54', plain,
% 5.91/6.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.91/6.17         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.91/6.17      inference('sup+', [status(thm)], ['11', '13'])).
% 5.91/6.17  thf('55', plain,
% 5.91/6.17      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.91/6.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.91/6.17  thf('56', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('57', plain,
% 5.91/6.17      (![X11 : $i, X12 : $i]:
% 5.91/6.17         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 5.91/6.17      inference('cnf', [status(esa)], [t3_subset])).
% 5.91/6.17  thf('58', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 5.91/6.17      inference('sup-', [status(thm)], ['56', '57'])).
% 5.91/6.17  thf('59', plain,
% 5.91/6.17      (![X3 : $i, X4 : $i, X5 : $i]:
% 5.91/6.17         (~ (r2_hidden @ X3 @ X4)
% 5.91/6.17          | (r2_hidden @ X3 @ X5)
% 5.91/6.17          | ~ (r1_tarski @ X4 @ X5))),
% 5.91/6.17      inference('cnf', [status(esa)], [d3_tarski])).
% 5.91/6.17  thf('60', plain,
% 5.91/6.17      (![X0 : $i]:
% 5.91/6.17         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 5.91/6.17          | ~ (r2_hidden @ X0 @ sk_D))),
% 5.91/6.17      inference('sup-', [status(thm)], ['58', '59'])).
% 5.91/6.17  thf('61', plain,
% 5.91/6.17      (((v1_xboole_0 @ sk_D)
% 5.91/6.17        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('sup-', [status(thm)], ['55', '60'])).
% 5.91/6.17  thf('62', plain,
% 5.91/6.17      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.91/6.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.91/6.17  thf('63', plain,
% 5.91/6.17      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('sup-', [status(thm)], ['61', '62'])).
% 5.91/6.17  thf('64', plain,
% 5.91/6.17      (![X0 : $i]:
% 5.91/6.17         (~ (v1_xboole_0 @ k1_xboole_0)
% 5.91/6.17          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 5.91/6.17          | (v1_xboole_0 @ sk_D))),
% 5.91/6.17      inference('sup-', [status(thm)], ['54', '63'])).
% 5.91/6.17  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.91/6.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.91/6.17  thf('66', plain,
% 5.91/6.17      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 5.91/6.17      inference('demod', [status(thm)], ['64', '65'])).
% 5.91/6.17  thf('67', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 5.91/6.17      inference('clc', [status(thm)], ['53', '66'])).
% 5.91/6.17  thf('68', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 5.91/6.17      inference('demod', [status(thm)], ['10', '67'])).
% 5.91/6.17  thf('69', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.91/6.17      inference('demod', [status(thm)], ['7', '68'])).
% 5.91/6.17  thf('70', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('71', plain,
% 5.91/6.17      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.91/6.17         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 5.91/6.17          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 5.91/6.17          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.91/6.17  thf('72', plain,
% 5.91/6.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 5.91/6.17        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 5.91/6.17      inference('sup-', [status(thm)], ['70', '71'])).
% 5.91/6.17  thf('73', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('74', plain,
% 5.91/6.17      (![X22 : $i, X23 : $i, X24 : $i]:
% 5.91/6.17         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 5.91/6.17          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 5.91/6.17      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.91/6.17  thf('75', plain,
% 5.91/6.17      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 5.91/6.17      inference('sup-', [status(thm)], ['73', '74'])).
% 5.91/6.17  thf('76', plain,
% 5.91/6.17      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 5.91/6.17        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 5.91/6.17      inference('demod', [status(thm)], ['72', '75'])).
% 5.91/6.17  thf('77', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('78', plain,
% 5.91/6.17      (![X35 : $i, X36 : $i, X37 : $i]:
% 5.91/6.17         (~ (zip_tseitin_0 @ X35 @ X36)
% 5.91/6.17          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 5.91/6.17          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.91/6.17  thf('79', plain,
% 5.91/6.17      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 5.91/6.17        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 5.91/6.17      inference('sup-', [status(thm)], ['77', '78'])).
% 5.91/6.17  thf('80', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 5.91/6.17      inference('clc', [status(thm)], ['53', '66'])).
% 5.91/6.17  thf('81', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 5.91/6.17      inference('demod', [status(thm)], ['79', '80'])).
% 5.91/6.17  thf('82', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 5.91/6.17      inference('demod', [status(thm)], ['76', '81'])).
% 5.91/6.17  thf(t9_funct_1, axiom,
% 5.91/6.17    (![A:$i]:
% 5.91/6.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.91/6.17       ( ![B:$i]:
% 5.91/6.17         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.91/6.17           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 5.91/6.17               ( ![C:$i]:
% 5.91/6.17                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 5.91/6.17                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 5.91/6.17             ( ( A ) = ( B ) ) ) ) ) ))).
% 5.91/6.17  thf('83', plain,
% 5.91/6.17      (![X17 : $i, X18 : $i]:
% 5.91/6.17         (~ (v1_relat_1 @ X17)
% 5.91/6.17          | ~ (v1_funct_1 @ X17)
% 5.91/6.17          | ((X18) = (X17))
% 5.91/6.17          | (r2_hidden @ (sk_C_1 @ X17 @ X18) @ (k1_relat_1 @ X18))
% 5.91/6.17          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 5.91/6.17          | ~ (v1_funct_1 @ X18)
% 5.91/6.17          | ~ (v1_relat_1 @ X18))),
% 5.91/6.17      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.91/6.17  thf('84', plain,
% 5.91/6.17      (![X0 : $i]:
% 5.91/6.17         (((sk_A) != (k1_relat_1 @ X0))
% 5.91/6.17          | ~ (v1_relat_1 @ sk_C_2)
% 5.91/6.17          | ~ (v1_funct_1 @ sk_C_2)
% 5.91/6.17          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 5.91/6.17          | ((sk_C_2) = (X0))
% 5.91/6.17          | ~ (v1_funct_1 @ X0)
% 5.91/6.17          | ~ (v1_relat_1 @ X0))),
% 5.91/6.17      inference('sup-', [status(thm)], ['82', '83'])).
% 5.91/6.17  thf('85', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf(cc1_relset_1, axiom,
% 5.91/6.17    (![A:$i,B:$i,C:$i]:
% 5.91/6.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.91/6.17       ( v1_relat_1 @ C ) ))).
% 5.91/6.17  thf('86', plain,
% 5.91/6.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.91/6.17         ((v1_relat_1 @ X19)
% 5.91/6.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 5.91/6.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.91/6.17  thf('87', plain, ((v1_relat_1 @ sk_C_2)),
% 5.91/6.17      inference('sup-', [status(thm)], ['85', '86'])).
% 5.91/6.17  thf('88', plain, ((v1_funct_1 @ sk_C_2)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('89', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 5.91/6.17      inference('demod', [status(thm)], ['76', '81'])).
% 5.91/6.17  thf('90', plain,
% 5.91/6.17      (![X0 : $i]:
% 5.91/6.17         (((sk_A) != (k1_relat_1 @ X0))
% 5.91/6.17          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 5.91/6.17          | ((sk_C_2) = (X0))
% 5.91/6.17          | ~ (v1_funct_1 @ X0)
% 5.91/6.17          | ~ (v1_relat_1 @ X0))),
% 5.91/6.17      inference('demod', [status(thm)], ['84', '87', '88', '89'])).
% 5.91/6.17  thf('91', plain,
% 5.91/6.17      ((((sk_A) != (sk_A))
% 5.91/6.17        | ~ (v1_relat_1 @ sk_D)
% 5.91/6.17        | ~ (v1_funct_1 @ sk_D)
% 5.91/6.17        | ((sk_C_2) = (sk_D))
% 5.91/6.17        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 5.91/6.17      inference('sup-', [status(thm)], ['69', '90'])).
% 5.91/6.17  thf('92', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('93', plain,
% 5.91/6.17      (![X19 : $i, X20 : $i, X21 : $i]:
% 5.91/6.17         ((v1_relat_1 @ X19)
% 5.91/6.17          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 5.91/6.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.91/6.17  thf('94', plain, ((v1_relat_1 @ sk_D)),
% 5.91/6.17      inference('sup-', [status(thm)], ['92', '93'])).
% 5.91/6.17  thf('95', plain, ((v1_funct_1 @ sk_D)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('96', plain,
% 5.91/6.17      ((((sk_A) != (sk_A))
% 5.91/6.17        | ((sk_C_2) = (sk_D))
% 5.91/6.17        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 5.91/6.17      inference('demod', [status(thm)], ['91', '94', '95'])).
% 5.91/6.17  thf('97', plain,
% 5.91/6.17      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 5.91/6.17      inference('simplify', [status(thm)], ['96'])).
% 5.91/6.17  thf('98', plain,
% 5.91/6.17      (![X38 : $i]:
% 5.91/6.17         (((k1_funct_1 @ sk_C_2 @ X38) = (k1_funct_1 @ sk_D @ X38))
% 5.91/6.17          | ~ (r2_hidden @ X38 @ sk_A))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('99', plain,
% 5.91/6.17      ((((sk_C_2) = (sk_D))
% 5.91/6.17        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.91/6.17            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 5.91/6.17      inference('sup-', [status(thm)], ['97', '98'])).
% 5.91/6.17  thf('100', plain,
% 5.91/6.17      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.91/6.17         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 5.91/6.17      inference('condensation', [status(thm)], ['99'])).
% 5.91/6.17  thf('101', plain,
% 5.91/6.17      (![X17 : $i, X18 : $i]:
% 5.91/6.17         (~ (v1_relat_1 @ X17)
% 5.91/6.17          | ~ (v1_funct_1 @ X17)
% 5.91/6.17          | ((X18) = (X17))
% 5.91/6.17          | ((k1_funct_1 @ X18 @ (sk_C_1 @ X17 @ X18))
% 5.91/6.17              != (k1_funct_1 @ X17 @ (sk_C_1 @ X17 @ X18)))
% 5.91/6.17          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 5.91/6.17          | ~ (v1_funct_1 @ X18)
% 5.91/6.17          | ~ (v1_relat_1 @ X18))),
% 5.91/6.17      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.91/6.17  thf('102', plain,
% 5.91/6.17      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.91/6.17          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 5.91/6.17        | ~ (v1_relat_1 @ sk_C_2)
% 5.91/6.17        | ~ (v1_funct_1 @ sk_C_2)
% 5.91/6.17        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 5.91/6.17        | ((sk_C_2) = (sk_D))
% 5.91/6.17        | ~ (v1_funct_1 @ sk_D)
% 5.91/6.17        | ~ (v1_relat_1 @ sk_D))),
% 5.91/6.17      inference('sup-', [status(thm)], ['100', '101'])).
% 5.91/6.17  thf('103', plain, ((v1_relat_1 @ sk_C_2)),
% 5.91/6.17      inference('sup-', [status(thm)], ['85', '86'])).
% 5.91/6.17  thf('104', plain, ((v1_funct_1 @ sk_C_2)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('105', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 5.91/6.17      inference('demod', [status(thm)], ['76', '81'])).
% 5.91/6.17  thf('106', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.91/6.17      inference('demod', [status(thm)], ['7', '68'])).
% 5.91/6.17  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 5.91/6.17      inference('sup-', [status(thm)], ['92', '93'])).
% 5.91/6.17  thf('109', plain,
% 5.91/6.17      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 5.91/6.17          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 5.91/6.17        | ((sk_A) != (sk_A))
% 5.91/6.17        | ((sk_C_2) = (sk_D)))),
% 5.91/6.17      inference('demod', [status(thm)],
% 5.91/6.17                ['102', '103', '104', '105', '106', '107', '108'])).
% 5.91/6.17  thf('110', plain, (((sk_C_2) = (sk_D))),
% 5.91/6.17      inference('simplify', [status(thm)], ['109'])).
% 5.91/6.17  thf('111', plain,
% 5.91/6.17      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.91/6.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.91/6.17  thf('112', plain,
% 5.91/6.17      (![X26 : $i, X27 : $i, X28 : $i]:
% 5.91/6.17         ((r2_relset_1 @ X26 @ X27 @ X28 @ X28)
% 5.91/6.17          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 5.91/6.17      inference('simplify', [status(thm)], ['46'])).
% 5.91/6.17  thf('113', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 5.91/6.17      inference('sup-', [status(thm)], ['111', '112'])).
% 5.91/6.17  thf('114', plain, ($false),
% 5.91/6.17      inference('demod', [status(thm)], ['0', '110', '113'])).
% 5.91/6.17  
% 5.91/6.17  % SZS output end Refutation
% 5.91/6.17  
% 5.91/6.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

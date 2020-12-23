%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UbmZTPN6lk

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:38 EST 2020

% Result     : Theorem 5.05s
% Output     : Refutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 533 expanded)
%              Number of leaves         :   38 ( 177 expanded)
%              Depth                    :   22
%              Number of atoms          : 1003 (6441 expanded)
%              Number of equality atoms :   73 ( 316 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_relset_1 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','33'])).

thf('35',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ~ ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','13'])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['37','48'])).

thf('50',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','49'])).

thf('51',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['37','48'])).

thf('63',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','63'])).

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

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('68',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('69',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','69','70','71'])).

thf('73',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['73','76','77'])).

thf('79',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X35: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X35 )
        = ( k1_funct_1 @ sk_D @ X35 ) )
      | ~ ( r2_hidden @ X35 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['81'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( ( k1_funct_1 @ X16 @ ( sk_C @ X15 @ X16 ) )
       != ( k1_funct_1 @ X15 @ ( sk_C @ X15 @ X16 ) ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('84',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('86',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('88',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','50'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('91',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','89','90'])).

thf('92',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_relset_1 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UbmZTPN6lk
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.05/5.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.05/5.25  % Solved by: fo/fo7.sh
% 5.05/5.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.05/5.25  % done 3770 iterations in 4.793s
% 5.05/5.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.05/5.25  % SZS output start Refutation
% 5.05/5.25  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.05/5.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.05/5.25  thf(sk_B_1_type, type, sk_B_1: $i).
% 5.05/5.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.05/5.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.05/5.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.05/5.25  thf(sk_D_type, type, sk_D: $i).
% 5.05/5.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 5.05/5.25  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 5.05/5.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.05/5.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.05/5.25  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.05/5.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.05/5.25  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.05/5.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.05/5.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.05/5.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.05/5.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.05/5.25  thf(sk_B_type, type, sk_B: $i > $i).
% 5.05/5.25  thf(sk_A_type, type, sk_A: $i).
% 5.05/5.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.05/5.25  thf(t18_funct_2, conjecture,
% 5.05/5.25    (![A:$i,B:$i,C:$i]:
% 5.05/5.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.05/5.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.05/5.25       ( ![D:$i]:
% 5.05/5.25         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.05/5.25             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.05/5.25           ( ( ![E:$i]:
% 5.05/5.25               ( ( r2_hidden @ E @ A ) =>
% 5.05/5.25                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.05/5.25             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 5.05/5.25  thf(zf_stmt_0, negated_conjecture,
% 5.05/5.25    (~( ![A:$i,B:$i,C:$i]:
% 5.05/5.25        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.05/5.25            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.05/5.25          ( ![D:$i]:
% 5.05/5.25            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.05/5.25                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.05/5.25              ( ( ![E:$i]:
% 5.05/5.25                  ( ( r2_hidden @ E @ A ) =>
% 5.05/5.25                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 5.05/5.25                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 5.05/5.25    inference('cnf.neg', [status(esa)], [t18_funct_2])).
% 5.05/5.25  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(d1_funct_2, axiom,
% 5.05/5.25    (![A:$i,B:$i,C:$i]:
% 5.05/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.05/5.25       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.05/5.25           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 5.05/5.25             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 5.05/5.25         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.05/5.25           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 5.05/5.25             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 5.05/5.25  thf(zf_stmt_1, axiom,
% 5.05/5.25    (![C:$i,B:$i,A:$i]:
% 5.05/5.25     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 5.05/5.25       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 5.05/5.25  thf('2', plain,
% 5.05/5.25      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.05/5.25         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 5.05/5.25          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 5.05/5.25          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.05/5.25  thf('3', plain,
% 5.05/5.25      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.05/5.25        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['1', '2'])).
% 5.05/5.25  thf('4', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(redefinition_k1_relset_1, axiom,
% 5.05/5.25    (![A:$i,B:$i,C:$i]:
% 5.05/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.05/5.25       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 5.05/5.25  thf('5', plain,
% 5.05/5.25      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.05/5.25         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 5.05/5.25          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.05/5.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.05/5.25  thf('6', plain,
% 5.05/5.25      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 5.05/5.25      inference('sup-', [status(thm)], ['4', '5'])).
% 5.05/5.25  thf('7', plain,
% 5.05/5.25      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.05/5.25        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 5.05/5.25      inference('demod', [status(thm)], ['3', '6'])).
% 5.05/5.25  thf('8', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 5.05/5.25  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.05/5.25  thf(zf_stmt_4, axiom,
% 5.05/5.25    (![B:$i,A:$i]:
% 5.05/5.25     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 5.05/5.25       ( zip_tseitin_0 @ B @ A ) ))).
% 5.05/5.25  thf(zf_stmt_5, axiom,
% 5.05/5.25    (![A:$i,B:$i,C:$i]:
% 5.05/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.05/5.25       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 5.05/5.25         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 5.05/5.25           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 5.05/5.25             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 5.05/5.25  thf('9', plain,
% 5.05/5.25      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.05/5.25         (~ (zip_tseitin_0 @ X32 @ X33)
% 5.05/5.25          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 5.05/5.25          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.05/5.25  thf('10', plain,
% 5.05/5.25      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 5.05/5.25        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 5.05/5.25      inference('sup-', [status(thm)], ['8', '9'])).
% 5.05/5.25  thf('11', plain,
% 5.05/5.25      (![X27 : $i, X28 : $i]:
% 5.05/5.25         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.05/5.25  thf(t113_zfmisc_1, axiom,
% 5.05/5.25    (![A:$i,B:$i]:
% 5.05/5.25     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 5.05/5.25       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 5.05/5.25  thf('12', plain,
% 5.05/5.25      (![X6 : $i, X7 : $i]:
% 5.05/5.25         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 5.05/5.25      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 5.05/5.25  thf('13', plain,
% 5.05/5.25      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 5.05/5.25      inference('simplify', [status(thm)], ['12'])).
% 5.05/5.25  thf('14', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.05/5.25         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.05/5.25      inference('sup+', [status(thm)], ['11', '13'])).
% 5.05/5.25  thf(d1_xboole_0, axiom,
% 5.05/5.25    (![A:$i]:
% 5.05/5.25     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 5.05/5.25  thf('15', plain,
% 5.05/5.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.05/5.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.05/5.25  thf('16', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(l3_subset_1, axiom,
% 5.05/5.25    (![A:$i,B:$i]:
% 5.05/5.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.05/5.25       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 5.05/5.25  thf('17', plain,
% 5.05/5.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.05/5.25         (~ (r2_hidden @ X8 @ X9)
% 5.05/5.25          | (r2_hidden @ X8 @ X10)
% 5.05/5.25          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 5.05/5.25      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.05/5.25  thf('18', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 5.05/5.25          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 5.05/5.25      inference('sup-', [status(thm)], ['16', '17'])).
% 5.05/5.25  thf('19', plain,
% 5.05/5.25      (((v1_xboole_0 @ sk_C_1)
% 5.05/5.25        | (r2_hidden @ (sk_B @ sk_C_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['15', '18'])).
% 5.05/5.25  thf('20', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.05/5.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.05/5.25  thf('21', plain,
% 5.05/5.25      (((v1_xboole_0 @ sk_C_1)
% 5.05/5.25        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['19', '20'])).
% 5.05/5.25  thf('22', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         (~ (v1_xboole_0 @ k1_xboole_0)
% 5.05/5.25          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 5.05/5.25          | (v1_xboole_0 @ sk_C_1))),
% 5.05/5.25      inference('sup-', [status(thm)], ['14', '21'])).
% 5.05/5.25  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 5.05/5.25  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.05/5.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.05/5.25  thf('24', plain,
% 5.05/5.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 5.05/5.25      inference('demod', [status(thm)], ['22', '23'])).
% 5.05/5.25  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.05/5.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.05/5.25  thf(t8_boole, axiom,
% 5.05/5.25    (![A:$i,B:$i]:
% 5.05/5.25     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 5.05/5.25  thf('26', plain,
% 5.05/5.25      (![X3 : $i, X4 : $i]:
% 5.05/5.25         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 5.05/5.25      inference('cnf', [status(esa)], [t8_boole])).
% 5.05/5.25  thf('27', plain,
% 5.05/5.25      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.05/5.25      inference('sup-', [status(thm)], ['25', '26'])).
% 5.05/5.25  thf('28', plain,
% 5.05/5.25      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 5.05/5.25      inference('sup-', [status(thm)], ['25', '26'])).
% 5.05/5.25  thf(t4_subset_1, axiom,
% 5.05/5.25    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 5.05/5.25  thf('29', plain,
% 5.05/5.25      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 5.05/5.25      inference('cnf', [status(esa)], [t4_subset_1])).
% 5.05/5.25  thf(redefinition_r2_relset_1, axiom,
% 5.05/5.25    (![A:$i,B:$i,C:$i,D:$i]:
% 5.05/5.25     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.05/5.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.05/5.25       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.05/5.25  thf('30', plain,
% 5.05/5.25      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 5.05/5.25         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 5.05/5.25          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 5.05/5.25          | (r2_relset_1 @ X24 @ X25 @ X23 @ X26)
% 5.05/5.25          | ((X23) != (X26)))),
% 5.05/5.25      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.05/5.25  thf('31', plain,
% 5.05/5.25      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.05/5.25         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 5.05/5.25          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.05/5.25      inference('simplify', [status(thm)], ['30'])).
% 5.05/5.25  thf('32', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 5.05/5.25      inference('sup-', [status(thm)], ['29', '31'])).
% 5.05/5.25  thf('33', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.05/5.25         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 5.05/5.25      inference('sup+', [status(thm)], ['28', '32'])).
% 5.05/5.25  thf('34', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.05/5.25         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 5.05/5.25          | ~ (v1_xboole_0 @ X0)
% 5.05/5.25          | ~ (v1_xboole_0 @ X1))),
% 5.05/5.25      inference('sup+', [status(thm)], ['27', '33'])).
% 5.05/5.25  thf('35', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('36', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_D))),
% 5.05/5.25      inference('sup-', [status(thm)], ['34', '35'])).
% 5.05/5.25  thf('37', plain,
% 5.05/5.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | ~ (v1_xboole_0 @ sk_D))),
% 5.05/5.25      inference('sup-', [status(thm)], ['24', '36'])).
% 5.05/5.25  thf('38', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.05/5.25         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 5.05/5.25      inference('sup+', [status(thm)], ['11', '13'])).
% 5.05/5.25  thf('39', plain,
% 5.05/5.25      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 5.05/5.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.05/5.25  thf('40', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('41', plain,
% 5.05/5.25      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.05/5.25         (~ (r2_hidden @ X8 @ X9)
% 5.05/5.25          | (r2_hidden @ X8 @ X10)
% 5.05/5.25          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 5.05/5.25      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.05/5.25  thf('42', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 5.05/5.25          | ~ (r2_hidden @ X0 @ sk_D))),
% 5.05/5.25      inference('sup-', [status(thm)], ['40', '41'])).
% 5.05/5.25  thf('43', plain,
% 5.05/5.25      (((v1_xboole_0 @ sk_D)
% 5.05/5.25        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['39', '42'])).
% 5.05/5.25  thf('44', plain,
% 5.05/5.25      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 5.05/5.25      inference('cnf', [status(esa)], [d1_xboole_0])).
% 5.05/5.25  thf('45', plain,
% 5.05/5.25      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['43', '44'])).
% 5.05/5.25  thf('46', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         (~ (v1_xboole_0 @ k1_xboole_0)
% 5.05/5.25          | (zip_tseitin_0 @ sk_B_1 @ X0)
% 5.05/5.25          | (v1_xboole_0 @ sk_D))),
% 5.05/5.25      inference('sup-', [status(thm)], ['38', '45'])).
% 5.05/5.25  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 5.05/5.25      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 5.05/5.25  thf('48', plain,
% 5.05/5.25      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 5.05/5.25      inference('demod', [status(thm)], ['46', '47'])).
% 5.05/5.25  thf('49', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 5.05/5.25      inference('clc', [status(thm)], ['37', '48'])).
% 5.05/5.25  thf('50', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 5.05/5.25      inference('demod', [status(thm)], ['10', '49'])).
% 5.05/5.25  thf('51', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.05/5.25      inference('demod', [status(thm)], ['7', '50'])).
% 5.05/5.25  thf('52', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('53', plain,
% 5.05/5.25      (![X29 : $i, X30 : $i, X31 : $i]:
% 5.05/5.25         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 5.05/5.25          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 5.05/5.25          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_1])).
% 5.05/5.25  thf('54', plain,
% 5.05/5.25      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 5.05/5.25        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 5.05/5.25      inference('sup-', [status(thm)], ['52', '53'])).
% 5.05/5.25  thf('55', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('56', plain,
% 5.05/5.25      (![X20 : $i, X21 : $i, X22 : $i]:
% 5.05/5.25         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 5.05/5.25          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 5.05/5.25      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 5.05/5.25  thf('57', plain,
% 5.05/5.25      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 5.05/5.25      inference('sup-', [status(thm)], ['55', '56'])).
% 5.05/5.25  thf('58', plain,
% 5.05/5.25      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 5.05/5.25        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 5.05/5.25      inference('demod', [status(thm)], ['54', '57'])).
% 5.05/5.25  thf('59', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('60', plain,
% 5.05/5.25      (![X32 : $i, X33 : $i, X34 : $i]:
% 5.05/5.25         (~ (zip_tseitin_0 @ X32 @ X33)
% 5.05/5.25          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 5.05/5.25          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.05/5.25  thf('61', plain,
% 5.05/5.25      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 5.05/5.25        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 5.05/5.25      inference('sup-', [status(thm)], ['59', '60'])).
% 5.05/5.25  thf('62', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 5.05/5.25      inference('clc', [status(thm)], ['37', '48'])).
% 5.05/5.25  thf('63', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 5.05/5.25      inference('demod', [status(thm)], ['61', '62'])).
% 5.05/5.25  thf('64', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.05/5.25      inference('demod', [status(thm)], ['58', '63'])).
% 5.05/5.25  thf(t9_funct_1, axiom,
% 5.05/5.25    (![A:$i]:
% 5.05/5.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.05/5.25       ( ![B:$i]:
% 5.05/5.25         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.05/5.25           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 5.05/5.25               ( ![C:$i]:
% 5.05/5.25                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 5.05/5.25                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 5.05/5.25             ( ( A ) = ( B ) ) ) ) ) ))).
% 5.05/5.25  thf('65', plain,
% 5.05/5.25      (![X15 : $i, X16 : $i]:
% 5.05/5.25         (~ (v1_relat_1 @ X15)
% 5.05/5.25          | ~ (v1_funct_1 @ X15)
% 5.05/5.25          | ((X16) = (X15))
% 5.05/5.25          | (r2_hidden @ (sk_C @ X15 @ X16) @ (k1_relat_1 @ X16))
% 5.05/5.25          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 5.05/5.25          | ~ (v1_funct_1 @ X16)
% 5.05/5.25          | ~ (v1_relat_1 @ X16))),
% 5.05/5.25      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.05/5.25  thf('66', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         (((sk_A) != (k1_relat_1 @ X0))
% 5.05/5.25          | ~ (v1_relat_1 @ sk_C_1)
% 5.05/5.25          | ~ (v1_funct_1 @ sk_C_1)
% 5.05/5.25          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 5.05/5.25          | ((sk_C_1) = (X0))
% 5.05/5.25          | ~ (v1_funct_1 @ X0)
% 5.05/5.25          | ~ (v1_relat_1 @ X0))),
% 5.05/5.25      inference('sup-', [status(thm)], ['64', '65'])).
% 5.05/5.25  thf('67', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf(cc1_relset_1, axiom,
% 5.05/5.25    (![A:$i,B:$i,C:$i]:
% 5.05/5.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.05/5.25       ( v1_relat_1 @ C ) ))).
% 5.05/5.25  thf('68', plain,
% 5.05/5.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.05/5.25         ((v1_relat_1 @ X17)
% 5.05/5.25          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.05/5.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.05/5.25  thf('69', plain, ((v1_relat_1 @ sk_C_1)),
% 5.05/5.25      inference('sup-', [status(thm)], ['67', '68'])).
% 5.05/5.25  thf('70', plain, ((v1_funct_1 @ sk_C_1)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('71', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.05/5.25      inference('demod', [status(thm)], ['58', '63'])).
% 5.05/5.25  thf('72', plain,
% 5.05/5.25      (![X0 : $i]:
% 5.05/5.25         (((sk_A) != (k1_relat_1 @ X0))
% 5.05/5.25          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 5.05/5.25          | ((sk_C_1) = (X0))
% 5.05/5.25          | ~ (v1_funct_1 @ X0)
% 5.05/5.25          | ~ (v1_relat_1 @ X0))),
% 5.05/5.25      inference('demod', [status(thm)], ['66', '69', '70', '71'])).
% 5.05/5.25  thf('73', plain,
% 5.05/5.25      ((((sk_A) != (sk_A))
% 5.05/5.25        | ~ (v1_relat_1 @ sk_D)
% 5.05/5.25        | ~ (v1_funct_1 @ sk_D)
% 5.05/5.25        | ((sk_C_1) = (sk_D))
% 5.05/5.25        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 5.05/5.25      inference('sup-', [status(thm)], ['51', '72'])).
% 5.05/5.25  thf('74', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('75', plain,
% 5.05/5.25      (![X17 : $i, X18 : $i, X19 : $i]:
% 5.05/5.25         ((v1_relat_1 @ X17)
% 5.05/5.25          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 5.05/5.25      inference('cnf', [status(esa)], [cc1_relset_1])).
% 5.05/5.25  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 5.05/5.25      inference('sup-', [status(thm)], ['74', '75'])).
% 5.05/5.25  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('78', plain,
% 5.05/5.25      ((((sk_A) != (sk_A))
% 5.05/5.25        | ((sk_C_1) = (sk_D))
% 5.05/5.25        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 5.05/5.25      inference('demod', [status(thm)], ['73', '76', '77'])).
% 5.05/5.25  thf('79', plain,
% 5.05/5.25      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 5.05/5.25      inference('simplify', [status(thm)], ['78'])).
% 5.05/5.25  thf('80', plain,
% 5.05/5.25      (![X35 : $i]:
% 5.05/5.25         (((k1_funct_1 @ sk_C_1 @ X35) = (k1_funct_1 @ sk_D @ X35))
% 5.05/5.25          | ~ (r2_hidden @ X35 @ sk_A))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('81', plain,
% 5.05/5.25      ((((sk_C_1) = (sk_D))
% 5.05/5.25        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.05/5.25            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 5.05/5.25      inference('sup-', [status(thm)], ['79', '80'])).
% 5.05/5.25  thf('82', plain,
% 5.05/5.25      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.05/5.25         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 5.05/5.25      inference('condensation', [status(thm)], ['81'])).
% 5.05/5.25  thf('83', plain,
% 5.05/5.25      (![X15 : $i, X16 : $i]:
% 5.05/5.25         (~ (v1_relat_1 @ X15)
% 5.05/5.25          | ~ (v1_funct_1 @ X15)
% 5.05/5.25          | ((X16) = (X15))
% 5.05/5.25          | ((k1_funct_1 @ X16 @ (sk_C @ X15 @ X16))
% 5.05/5.25              != (k1_funct_1 @ X15 @ (sk_C @ X15 @ X16)))
% 5.05/5.25          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 5.05/5.25          | ~ (v1_funct_1 @ X16)
% 5.05/5.25          | ~ (v1_relat_1 @ X16))),
% 5.05/5.25      inference('cnf', [status(esa)], [t9_funct_1])).
% 5.05/5.25  thf('84', plain,
% 5.05/5.25      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.05/5.25          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 5.05/5.25        | ~ (v1_relat_1 @ sk_C_1)
% 5.05/5.25        | ~ (v1_funct_1 @ sk_C_1)
% 5.05/5.25        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 5.05/5.25        | ((sk_C_1) = (sk_D))
% 5.05/5.25        | ~ (v1_funct_1 @ sk_D)
% 5.05/5.25        | ~ (v1_relat_1 @ sk_D))),
% 5.05/5.25      inference('sup-', [status(thm)], ['82', '83'])).
% 5.05/5.25  thf('85', plain, ((v1_relat_1 @ sk_C_1)),
% 5.05/5.25      inference('sup-', [status(thm)], ['67', '68'])).
% 5.05/5.25  thf('86', plain, ((v1_funct_1 @ sk_C_1)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('87', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 5.05/5.25      inference('demod', [status(thm)], ['58', '63'])).
% 5.05/5.25  thf('88', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 5.05/5.25      inference('demod', [status(thm)], ['7', '50'])).
% 5.05/5.25  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('90', plain, ((v1_relat_1 @ sk_D)),
% 5.05/5.25      inference('sup-', [status(thm)], ['74', '75'])).
% 5.05/5.25  thf('91', plain,
% 5.05/5.25      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 5.05/5.25          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 5.05/5.25        | ((sk_A) != (sk_A))
% 5.05/5.25        | ((sk_C_1) = (sk_D)))),
% 5.05/5.25      inference('demod', [status(thm)],
% 5.05/5.25                ['84', '85', '86', '87', '88', '89', '90'])).
% 5.05/5.25  thf('92', plain, (((sk_C_1) = (sk_D))),
% 5.05/5.25      inference('simplify', [status(thm)], ['91'])).
% 5.05/5.25  thf('93', plain,
% 5.05/5.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 5.05/5.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.05/5.25  thf('94', plain,
% 5.05/5.25      (![X24 : $i, X25 : $i, X26 : $i]:
% 5.05/5.25         ((r2_relset_1 @ X24 @ X25 @ X26 @ X26)
% 5.05/5.25          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.05/5.25      inference('simplify', [status(thm)], ['30'])).
% 5.05/5.25  thf('95', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 5.05/5.25      inference('sup-', [status(thm)], ['93', '94'])).
% 5.05/5.25  thf('96', plain, ($false),
% 5.05/5.25      inference('demod', [status(thm)], ['0', '92', '95'])).
% 5.05/5.25  
% 5.05/5.25  % SZS output end Refutation
% 5.05/5.25  
% 5.05/5.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

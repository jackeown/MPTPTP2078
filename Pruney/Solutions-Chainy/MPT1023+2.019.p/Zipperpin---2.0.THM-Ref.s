%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vPxEtsKlG2

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:31 EST 2020

% Result     : Theorem 13.42s
% Output     : Refutation 13.51s
% Verified   : 
% Statistics : Number of formulae       :  178 (1158 expanded)
%              Number of leaves         :   41 ( 380 expanded)
%              Depth                    :   24
%              Number of atoms          : 1266 (11346 expanded)
%              Number of equality atoms :   88 ( 537 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
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
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('2',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['19','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('44',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','48'])).

thf('50',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    r1_tarski @ sk_C_2 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
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
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['51','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['67','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['27','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('84',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('86',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('89',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['83','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('93',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('95',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['91','98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['67','80'])).

thf('101',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['99','100'])).

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

thf('102',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( r2_hidden @ ( sk_C_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('105',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('106',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','106','107','108'])).

thf('110',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['82','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['110','113','114'])).

thf('116',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['115'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('117',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('118',plain,
    ( ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X38: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X38 )
        = ( k1_funct_1 @ sk_D @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['120'])).

thf('122',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_funct_1 @ X19 @ ( sk_C_1 @ X18 @ X19 ) )
       != ( k1_funct_1 @ X18 @ ( sk_C_1 @ X18 @ X19 ) ) )
      | ( ( k1_relat_1 @ X19 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('123',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['104','105'])).

thf('125',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('127',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['27','81'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['111','112'])).

thf('130',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['123','124','125','126','127','128','129'])).

thf('131',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('134',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['0','131','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vPxEtsKlG2
% 0.16/0.38  % Computer   : n024.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 13:19:51 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.39  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 13.42/13.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.42/13.68  % Solved by: fo/fo7.sh
% 13.42/13.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.42/13.68  % done 9300 iterations in 13.178s
% 13.42/13.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.42/13.68  % SZS output start Refutation
% 13.42/13.68  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 13.42/13.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 13.42/13.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.42/13.68  thf(sk_A_type, type, sk_A: $i).
% 13.42/13.68  thf(sk_D_type, type, sk_D: $i).
% 13.42/13.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.42/13.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.42/13.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.42/13.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 13.42/13.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.42/13.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 13.42/13.68  thf(sk_B_type, type, sk_B: $i > $i).
% 13.42/13.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 13.42/13.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 13.42/13.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 13.42/13.68  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 13.42/13.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 13.42/13.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.42/13.68  thf(sk_C_2_type, type, sk_C_2: $i).
% 13.42/13.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 13.42/13.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.42/13.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.42/13.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.42/13.68  thf(t113_funct_2, conjecture,
% 13.42/13.68    (![A:$i,B:$i,C:$i]:
% 13.42/13.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 13.42/13.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.42/13.68       ( ![D:$i]:
% 13.42/13.68         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 13.42/13.68             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.42/13.68           ( ( ![E:$i]:
% 13.42/13.68               ( ( m1_subset_1 @ E @ A ) =>
% 13.42/13.68                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 13.42/13.68             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 13.42/13.68  thf(zf_stmt_0, negated_conjecture,
% 13.42/13.68    (~( ![A:$i,B:$i,C:$i]:
% 13.42/13.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 13.42/13.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.42/13.68          ( ![D:$i]:
% 13.42/13.68            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 13.42/13.68                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.42/13.68              ( ( ![E:$i]:
% 13.42/13.68                  ( ( m1_subset_1 @ E @ A ) =>
% 13.42/13.68                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 13.42/13.68                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 13.42/13.68    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 13.42/13.68  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.42/13.68  thf(d1_funct_2, axiom,
% 13.42/13.68    (![A:$i,B:$i,C:$i]:
% 13.42/13.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.42/13.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.42/13.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 13.42/13.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 13.42/13.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.42/13.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 13.42/13.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 13.42/13.68  thf(zf_stmt_1, axiom,
% 13.42/13.68    (![B:$i,A:$i]:
% 13.42/13.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 13.42/13.68       ( zip_tseitin_0 @ B @ A ) ))).
% 13.42/13.68  thf('1', plain,
% 13.42/13.68      (![X30 : $i, X31 : $i]:
% 13.42/13.68         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 13.42/13.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 13.42/13.68  thf('2', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.42/13.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.42/13.68  thf('3', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 13.42/13.68      inference('sup+', [status(thm)], ['1', '2'])).
% 13.42/13.68  thf(d3_tarski, axiom,
% 13.42/13.68    (![A:$i,B:$i]:
% 13.42/13.68     ( ( r1_tarski @ A @ B ) <=>
% 13.42/13.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 13.42/13.68  thf('4', plain,
% 13.42/13.68      (![X4 : $i, X6 : $i]:
% 13.42/13.68         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 13.42/13.68      inference('cnf', [status(esa)], [d3_tarski])).
% 13.42/13.68  thf(d1_xboole_0, axiom,
% 13.42/13.68    (![A:$i]:
% 13.42/13.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 13.42/13.68  thf('5', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 13.42/13.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.42/13.68  thf('6', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.42/13.68      inference('sup-', [status(thm)], ['4', '5'])).
% 13.42/13.68  thf(t3_subset, axiom,
% 13.42/13.68    (![A:$i,B:$i]:
% 13.42/13.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 13.42/13.68  thf('7', plain,
% 13.42/13.68      (![X15 : $i, X17 : $i]:
% 13.42/13.68         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 13.42/13.68      inference('cnf', [status(esa)], [t3_subset])).
% 13.42/13.68  thf('8', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]:
% 13.42/13.68         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['6', '7'])).
% 13.42/13.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 13.42/13.68  thf(zf_stmt_3, axiom,
% 13.42/13.68    (![C:$i,B:$i,A:$i]:
% 13.42/13.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 13.42/13.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 13.42/13.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 13.42/13.68  thf(zf_stmt_5, axiom,
% 13.42/13.68    (![A:$i,B:$i,C:$i]:
% 13.42/13.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.42/13.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 13.42/13.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 13.42/13.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 13.42/13.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 13.42/13.68  thf('9', plain,
% 13.42/13.68      (![X35 : $i, X36 : $i, X37 : $i]:
% 13.42/13.68         (~ (zip_tseitin_0 @ X35 @ X36)
% 13.42/13.68          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 13.42/13.68          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.42/13.68  thf('10', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.42/13.68         (~ (v1_xboole_0 @ X2)
% 13.42/13.68          | (zip_tseitin_1 @ X2 @ X0 @ X1)
% 13.42/13.68          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 13.42/13.68      inference('sup-', [status(thm)], ['8', '9'])).
% 13.42/13.68  thf('11', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.42/13.68         ((v1_xboole_0 @ X1)
% 13.42/13.68          | (zip_tseitin_1 @ X2 @ X1 @ X0)
% 13.42/13.68          | ~ (v1_xboole_0 @ X2))),
% 13.42/13.68      inference('sup-', [status(thm)], ['3', '10'])).
% 13.42/13.68  thf('12', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.42/13.68  thf('13', plain,
% 13.42/13.68      (![X32 : $i, X33 : $i, X34 : $i]:
% 13.42/13.68         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 13.42/13.68          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 13.42/13.68          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 13.42/13.68  thf('14', plain,
% 13.42/13.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 13.42/13.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['12', '13'])).
% 13.42/13.68  thf('15', plain,
% 13.42/13.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.42/13.68  thf(redefinition_k1_relset_1, axiom,
% 13.42/13.68    (![A:$i,B:$i,C:$i]:
% 13.42/13.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.42/13.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 13.42/13.68  thf('16', plain,
% 13.42/13.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 13.42/13.68         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 13.42/13.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 13.42/13.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.42/13.68  thf('17', plain,
% 13.42/13.68      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 13.42/13.68      inference('sup-', [status(thm)], ['15', '16'])).
% 13.42/13.68  thf('18', plain,
% 13.42/13.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 13.42/13.68        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 13.42/13.68      inference('demod', [status(thm)], ['14', '17'])).
% 13.42/13.68  thf('19', plain,
% 13.42/13.68      ((~ (v1_xboole_0 @ sk_D)
% 13.42/13.68        | (v1_xboole_0 @ sk_B_1)
% 13.42/13.68        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['11', '18'])).
% 13.42/13.68  thf('20', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 13.42/13.68      inference('sup+', [status(thm)], ['1', '2'])).
% 13.42/13.68  thf('21', plain,
% 13.42/13.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.42/13.68  thf('22', plain,
% 13.42/13.68      (![X35 : $i, X36 : $i, X37 : $i]:
% 13.42/13.68         (~ (zip_tseitin_0 @ X35 @ X36)
% 13.42/13.68          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 13.42/13.68          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 13.42/13.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.42/13.68  thf('23', plain,
% 13.42/13.68      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 13.42/13.68        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 13.42/13.68      inference('sup-', [status(thm)], ['21', '22'])).
% 13.42/13.68  thf('24', plain,
% 13.42/13.68      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 13.42/13.68      inference('sup-', [status(thm)], ['20', '23'])).
% 13.42/13.68  thf('25', plain,
% 13.42/13.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 13.42/13.68        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 13.42/13.68      inference('demod', [status(thm)], ['14', '17'])).
% 13.42/13.68  thf('26', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['24', '25'])).
% 13.42/13.68  thf('27', plain, ((((sk_A) = (k1_relat_1 @ sk_D)) | (v1_xboole_0 @ sk_B_1))),
% 13.42/13.68      inference('clc', [status(thm)], ['19', '26'])).
% 13.42/13.68  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.42/13.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.42/13.68  thf('29', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.42/13.68      inference('sup-', [status(thm)], ['4', '5'])).
% 13.42/13.68  thf('30', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.42/13.68      inference('sup-', [status(thm)], ['4', '5'])).
% 13.42/13.68  thf(d10_xboole_0, axiom,
% 13.42/13.68    (![A:$i,B:$i]:
% 13.42/13.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.42/13.68  thf('31', plain,
% 13.42/13.68      (![X7 : $i, X9 : $i]:
% 13.42/13.68         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 13.42/13.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.42/13.68  thf('32', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]:
% 13.42/13.68         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['30', '31'])).
% 13.42/13.68  thf('33', plain,
% 13.42/13.68      (![X0 : $i, X1 : $i]:
% 13.42/13.68         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 13.42/13.68      inference('sup-', [status(thm)], ['29', '32'])).
% 13.42/13.68  thf('34', plain,
% 13.42/13.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['28', '33'])).
% 13.42/13.68  thf('35', plain,
% 13.42/13.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['28', '33'])).
% 13.42/13.68  thf('36', plain,
% 13.42/13.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.42/13.68      inference('sup-', [status(thm)], ['28', '33'])).
% 13.42/13.68  thf('37', plain,
% 13.42/13.68      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 13.42/13.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.42/13.68  thf('38', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 13.42/13.68      inference('simplify', [status(thm)], ['37'])).
% 13.42/13.68  thf('39', plain,
% 13.42/13.68      (![X15 : $i, X17 : $i]:
% 13.42/13.68         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 13.42/13.68      inference('cnf', [status(esa)], [t3_subset])).
% 13.42/13.68  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 13.42/13.68      inference('sup-', [status(thm)], ['38', '39'])).
% 13.42/13.68  thf(t113_zfmisc_1, axiom,
% 13.42/13.68    (![A:$i,B:$i]:
% 13.42/13.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 13.42/13.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 13.42/13.68  thf('41', plain,
% 13.42/13.68      (![X11 : $i, X12 : $i]:
% 13.42/13.68         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 13.42/13.68          | ((X12) != (k1_xboole_0)))),
% 13.42/13.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 13.42/13.68  thf('42', plain,
% 13.42/13.68      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 13.42/13.68      inference('simplify', [status(thm)], ['41'])).
% 13.42/13.68  thf(redefinition_r2_relset_1, axiom,
% 13.42/13.68    (![A:$i,B:$i,C:$i,D:$i]:
% 13.42/13.68     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.42/13.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.42/13.68       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 13.42/13.68  thf('43', plain,
% 13.42/13.68      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 13.42/13.68         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 13.42/13.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 13.42/13.68          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 13.42/13.68          | ((X26) != (X29)))),
% 13.42/13.68      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 13.42/13.68  thf('44', plain,
% 13.51/13.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 13.51/13.68         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 13.51/13.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 13.51/13.68      inference('simplify', [status(thm)], ['43'])).
% 13.51/13.68  thf('45', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i]:
% 13.51/13.68         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 13.51/13.68          | (r2_relset_1 @ X0 @ k1_xboole_0 @ X1 @ X1))),
% 13.51/13.68      inference('sup-', [status(thm)], ['42', '44'])).
% 13.51/13.68  thf('46', plain,
% 13.51/13.68      (![X0 : $i]: (r2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 13.51/13.68      inference('sup-', [status(thm)], ['40', '45'])).
% 13.51/13.68  thf('47', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i]:
% 13.51/13.68         ((r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 13.51/13.68          | ~ (v1_xboole_0 @ X0))),
% 13.51/13.68      inference('sup+', [status(thm)], ['36', '46'])).
% 13.51/13.68  thf('48', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.51/13.68         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 13.51/13.68          | ~ (v1_xboole_0 @ X0)
% 13.51/13.68          | ~ (v1_xboole_0 @ X1))),
% 13.51/13.68      inference('sup+', [status(thm)], ['35', '47'])).
% 13.51/13.68  thf('49', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 13.51/13.68         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 13.51/13.68          | ~ (v1_xboole_0 @ X0)
% 13.51/13.68          | ~ (v1_xboole_0 @ X2)
% 13.51/13.68          | ~ (v1_xboole_0 @ X1))),
% 13.51/13.68      inference('sup+', [status(thm)], ['34', '48'])).
% 13.51/13.68  thf('50', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('51', plain,
% 13.51/13.68      ((~ (v1_xboole_0 @ sk_C_2)
% 13.51/13.68        | ~ (v1_xboole_0 @ sk_B_1)
% 13.51/13.68        | ~ (v1_xboole_0 @ sk_D))),
% 13.51/13.68      inference('sup-', [status(thm)], ['49', '50'])).
% 13.51/13.68  thf('52', plain,
% 13.51/13.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['28', '33'])).
% 13.51/13.68  thf('53', plain,
% 13.51/13.68      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 13.51/13.68      inference('simplify', [status(thm)], ['41'])).
% 13.51/13.68  thf('54', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i]:
% 13.51/13.68         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.51/13.68      inference('sup+', [status(thm)], ['52', '53'])).
% 13.51/13.68  thf('55', plain,
% 13.51/13.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 13.51/13.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.51/13.68  thf('56', plain,
% 13.51/13.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('57', plain,
% 13.51/13.68      (![X15 : $i, X16 : $i]:
% 13.51/13.68         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 13.51/13.68      inference('cnf', [status(esa)], [t3_subset])).
% 13.51/13.68  thf('58', plain, ((r1_tarski @ sk_C_2 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 13.51/13.68      inference('sup-', [status(thm)], ['56', '57'])).
% 13.51/13.68  thf('59', plain,
% 13.51/13.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 13.51/13.68         (~ (r2_hidden @ X3 @ X4)
% 13.51/13.68          | (r2_hidden @ X3 @ X5)
% 13.51/13.68          | ~ (r1_tarski @ X4 @ X5))),
% 13.51/13.68      inference('cnf', [status(esa)], [d3_tarski])).
% 13.51/13.68  thf('60', plain,
% 13.51/13.68      (![X0 : $i]:
% 13.51/13.68         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 13.51/13.68          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 13.51/13.68      inference('sup-', [status(thm)], ['58', '59'])).
% 13.51/13.68  thf('61', plain,
% 13.51/13.68      (((v1_xboole_0 @ sk_C_2)
% 13.51/13.68        | (r2_hidden @ (sk_B @ sk_C_2) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['55', '60'])).
% 13.51/13.68  thf('62', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 13.51/13.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.51/13.68  thf('63', plain,
% 13.51/13.68      (((v1_xboole_0 @ sk_C_2)
% 13.51/13.68        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['61', '62'])).
% 13.51/13.68  thf('64', plain,
% 13.51/13.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 13.51/13.68        | ~ (v1_xboole_0 @ sk_B_1)
% 13.51/13.68        | (v1_xboole_0 @ sk_C_2))),
% 13.51/13.68      inference('sup-', [status(thm)], ['54', '63'])).
% 13.51/13.68  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.51/13.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.51/13.68  thf('66', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2))),
% 13.51/13.68      inference('demod', [status(thm)], ['64', '65'])).
% 13.51/13.68  thf('67', plain, ((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_B_1))),
% 13.51/13.68      inference('clc', [status(thm)], ['51', '66'])).
% 13.51/13.68  thf('68', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i]:
% 13.51/13.68         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.51/13.68      inference('sup+', [status(thm)], ['52', '53'])).
% 13.51/13.68  thf('69', plain,
% 13.51/13.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 13.51/13.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.51/13.68  thf('70', plain,
% 13.51/13.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('71', plain,
% 13.51/13.68      (![X15 : $i, X16 : $i]:
% 13.51/13.68         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 13.51/13.68      inference('cnf', [status(esa)], [t3_subset])).
% 13.51/13.68  thf('72', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 13.51/13.68      inference('sup-', [status(thm)], ['70', '71'])).
% 13.51/13.68  thf('73', plain,
% 13.51/13.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 13.51/13.68         (~ (r2_hidden @ X3 @ X4)
% 13.51/13.68          | (r2_hidden @ X3 @ X5)
% 13.51/13.68          | ~ (r1_tarski @ X4 @ X5))),
% 13.51/13.68      inference('cnf', [status(esa)], [d3_tarski])).
% 13.51/13.68  thf('74', plain,
% 13.51/13.68      (![X0 : $i]:
% 13.51/13.68         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 13.51/13.68          | ~ (r2_hidden @ X0 @ sk_D))),
% 13.51/13.68      inference('sup-', [status(thm)], ['72', '73'])).
% 13.51/13.68  thf('75', plain,
% 13.51/13.68      (((v1_xboole_0 @ sk_D)
% 13.51/13.68        | (r2_hidden @ (sk_B @ sk_D) @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['69', '74'])).
% 13.51/13.68  thf('76', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 13.51/13.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.51/13.68  thf('77', plain,
% 13.51/13.68      (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['75', '76'])).
% 13.51/13.68  thf('78', plain,
% 13.51/13.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 13.51/13.68        | ~ (v1_xboole_0 @ sk_B_1)
% 13.51/13.68        | (v1_xboole_0 @ sk_D))),
% 13.51/13.68      inference('sup-', [status(thm)], ['68', '77'])).
% 13.51/13.68  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.51/13.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.51/13.68  thf('80', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_D))),
% 13.51/13.68      inference('demod', [status(thm)], ['78', '79'])).
% 13.51/13.68  thf('81', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 13.51/13.68      inference('clc', [status(thm)], ['67', '80'])).
% 13.51/13.68  thf('82', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 13.51/13.68      inference('clc', [status(thm)], ['27', '81'])).
% 13.51/13.68  thf('83', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.51/13.68         ((v1_xboole_0 @ X1)
% 13.51/13.68          | (zip_tseitin_1 @ X2 @ X1 @ X0)
% 13.51/13.68          | ~ (v1_xboole_0 @ X2))),
% 13.51/13.68      inference('sup-', [status(thm)], ['3', '10'])).
% 13.51/13.68  thf('84', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('85', plain,
% 13.51/13.68      (![X32 : $i, X33 : $i, X34 : $i]:
% 13.51/13.68         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 13.51/13.68          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 13.51/13.68          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 13.51/13.68  thf('86', plain,
% 13.51/13.68      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 13.51/13.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['84', '85'])).
% 13.51/13.68  thf('87', plain,
% 13.51/13.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('88', plain,
% 13.51/13.68      (![X23 : $i, X24 : $i, X25 : $i]:
% 13.51/13.68         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 13.51/13.68          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 13.51/13.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 13.51/13.68  thf('89', plain,
% 13.51/13.68      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 13.51/13.68      inference('sup-', [status(thm)], ['87', '88'])).
% 13.51/13.68  thf('90', plain,
% 13.51/13.68      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 13.51/13.68        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 13.51/13.68      inference('demod', [status(thm)], ['86', '89'])).
% 13.51/13.68  thf('91', plain,
% 13.51/13.68      ((~ (v1_xboole_0 @ sk_C_2)
% 13.51/13.68        | (v1_xboole_0 @ sk_B_1)
% 13.51/13.68        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['83', '90'])).
% 13.51/13.68  thf('92', plain,
% 13.51/13.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 13.51/13.68      inference('sup+', [status(thm)], ['1', '2'])).
% 13.51/13.68  thf('93', plain,
% 13.51/13.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('94', plain,
% 13.51/13.68      (![X35 : $i, X36 : $i, X37 : $i]:
% 13.51/13.68         (~ (zip_tseitin_0 @ X35 @ X36)
% 13.51/13.68          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 13.51/13.68          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 13.51/13.68  thf('95', plain,
% 13.51/13.68      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 13.51/13.68        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 13.51/13.68      inference('sup-', [status(thm)], ['93', '94'])).
% 13.51/13.68  thf('96', plain,
% 13.51/13.68      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 13.51/13.68      inference('sup-', [status(thm)], ['92', '95'])).
% 13.51/13.68  thf('97', plain,
% 13.51/13.68      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 13.51/13.68        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 13.51/13.68      inference('demod', [status(thm)], ['86', '89'])).
% 13.51/13.68  thf('98', plain,
% 13.51/13.68      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 13.51/13.68      inference('sup-', [status(thm)], ['96', '97'])).
% 13.51/13.68  thf('99', plain,
% 13.51/13.68      ((((sk_A) = (k1_relat_1 @ sk_C_2)) | (v1_xboole_0 @ sk_B_1))),
% 13.51/13.68      inference('clc', [status(thm)], ['91', '98'])).
% 13.51/13.68  thf('100', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 13.51/13.68      inference('clc', [status(thm)], ['67', '80'])).
% 13.51/13.68  thf('101', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 13.51/13.68      inference('clc', [status(thm)], ['99', '100'])).
% 13.51/13.68  thf(t9_funct_1, axiom,
% 13.51/13.68    (![A:$i]:
% 13.51/13.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 13.51/13.68       ( ![B:$i]:
% 13.51/13.68         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 13.51/13.68           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 13.51/13.68               ( ![C:$i]:
% 13.51/13.68                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 13.51/13.68                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 13.51/13.68             ( ( A ) = ( B ) ) ) ) ) ))).
% 13.51/13.68  thf('102', plain,
% 13.51/13.68      (![X18 : $i, X19 : $i]:
% 13.51/13.68         (~ (v1_relat_1 @ X18)
% 13.51/13.68          | ~ (v1_funct_1 @ X18)
% 13.51/13.68          | ((X19) = (X18))
% 13.51/13.68          | (r2_hidden @ (sk_C_1 @ X18 @ X19) @ (k1_relat_1 @ X19))
% 13.51/13.68          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 13.51/13.68          | ~ (v1_funct_1 @ X19)
% 13.51/13.68          | ~ (v1_relat_1 @ X19))),
% 13.51/13.68      inference('cnf', [status(esa)], [t9_funct_1])).
% 13.51/13.68  thf('103', plain,
% 13.51/13.68      (![X0 : $i]:
% 13.51/13.68         (((sk_A) != (k1_relat_1 @ X0))
% 13.51/13.68          | ~ (v1_relat_1 @ sk_C_2)
% 13.51/13.68          | ~ (v1_funct_1 @ sk_C_2)
% 13.51/13.68          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 13.51/13.68          | ((sk_C_2) = (X0))
% 13.51/13.68          | ~ (v1_funct_1 @ X0)
% 13.51/13.68          | ~ (v1_relat_1 @ X0))),
% 13.51/13.68      inference('sup-', [status(thm)], ['101', '102'])).
% 13.51/13.68  thf('104', plain,
% 13.51/13.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf(cc1_relset_1, axiom,
% 13.51/13.68    (![A:$i,B:$i,C:$i]:
% 13.51/13.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.51/13.68       ( v1_relat_1 @ C ) ))).
% 13.51/13.68  thf('105', plain,
% 13.51/13.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 13.51/13.68         ((v1_relat_1 @ X20)
% 13.51/13.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 13.51/13.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.51/13.68  thf('106', plain, ((v1_relat_1 @ sk_C_2)),
% 13.51/13.68      inference('sup-', [status(thm)], ['104', '105'])).
% 13.51/13.68  thf('107', plain, ((v1_funct_1 @ sk_C_2)),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('108', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 13.51/13.68      inference('clc', [status(thm)], ['99', '100'])).
% 13.51/13.68  thf('109', plain,
% 13.51/13.68      (![X0 : $i]:
% 13.51/13.68         (((sk_A) != (k1_relat_1 @ X0))
% 13.51/13.68          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 13.51/13.68          | ((sk_C_2) = (X0))
% 13.51/13.68          | ~ (v1_funct_1 @ X0)
% 13.51/13.68          | ~ (v1_relat_1 @ X0))),
% 13.51/13.68      inference('demod', [status(thm)], ['103', '106', '107', '108'])).
% 13.51/13.68  thf('110', plain,
% 13.51/13.68      ((((sk_A) != (sk_A))
% 13.51/13.68        | ~ (v1_relat_1 @ sk_D)
% 13.51/13.68        | ~ (v1_funct_1 @ sk_D)
% 13.51/13.68        | ((sk_C_2) = (sk_D))
% 13.51/13.68        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 13.51/13.68      inference('sup-', [status(thm)], ['82', '109'])).
% 13.51/13.68  thf('111', plain,
% 13.51/13.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('112', plain,
% 13.51/13.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 13.51/13.68         ((v1_relat_1 @ X20)
% 13.51/13.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 13.51/13.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 13.51/13.68  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 13.51/13.68      inference('sup-', [status(thm)], ['111', '112'])).
% 13.51/13.68  thf('114', plain, ((v1_funct_1 @ sk_D)),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('115', plain,
% 13.51/13.68      ((((sk_A) != (sk_A))
% 13.51/13.68        | ((sk_C_2) = (sk_D))
% 13.51/13.68        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 13.51/13.68      inference('demod', [status(thm)], ['110', '113', '114'])).
% 13.51/13.68  thf('116', plain,
% 13.51/13.68      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 13.51/13.68      inference('simplify', [status(thm)], ['115'])).
% 13.51/13.68  thf(t1_subset, axiom,
% 13.51/13.68    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 13.51/13.68  thf('117', plain,
% 13.51/13.68      (![X13 : $i, X14 : $i]:
% 13.51/13.68         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 13.51/13.68      inference('cnf', [status(esa)], [t1_subset])).
% 13.51/13.68  thf('118', plain,
% 13.51/13.68      ((((sk_C_2) = (sk_D)) | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 13.51/13.68      inference('sup-', [status(thm)], ['116', '117'])).
% 13.51/13.68  thf('119', plain,
% 13.51/13.68      (![X38 : $i]:
% 13.51/13.68         (((k1_funct_1 @ sk_C_2 @ X38) = (k1_funct_1 @ sk_D @ X38))
% 13.51/13.68          | ~ (m1_subset_1 @ X38 @ sk_A))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('120', plain,
% 13.51/13.68      ((((sk_C_2) = (sk_D))
% 13.51/13.68        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 13.51/13.68            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 13.51/13.68      inference('sup-', [status(thm)], ['118', '119'])).
% 13.51/13.68  thf('121', plain,
% 13.51/13.68      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 13.51/13.68         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 13.51/13.68      inference('condensation', [status(thm)], ['120'])).
% 13.51/13.68  thf('122', plain,
% 13.51/13.68      (![X18 : $i, X19 : $i]:
% 13.51/13.68         (~ (v1_relat_1 @ X18)
% 13.51/13.68          | ~ (v1_funct_1 @ X18)
% 13.51/13.68          | ((X19) = (X18))
% 13.51/13.68          | ((k1_funct_1 @ X19 @ (sk_C_1 @ X18 @ X19))
% 13.51/13.68              != (k1_funct_1 @ X18 @ (sk_C_1 @ X18 @ X19)))
% 13.51/13.68          | ((k1_relat_1 @ X19) != (k1_relat_1 @ X18))
% 13.51/13.68          | ~ (v1_funct_1 @ X19)
% 13.51/13.68          | ~ (v1_relat_1 @ X19))),
% 13.51/13.68      inference('cnf', [status(esa)], [t9_funct_1])).
% 13.51/13.68  thf('123', plain,
% 13.51/13.68      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 13.51/13.68          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 13.51/13.68        | ~ (v1_relat_1 @ sk_C_2)
% 13.51/13.68        | ~ (v1_funct_1 @ sk_C_2)
% 13.51/13.68        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 13.51/13.68        | ((sk_C_2) = (sk_D))
% 13.51/13.68        | ~ (v1_funct_1 @ sk_D)
% 13.51/13.68        | ~ (v1_relat_1 @ sk_D))),
% 13.51/13.68      inference('sup-', [status(thm)], ['121', '122'])).
% 13.51/13.68  thf('124', plain, ((v1_relat_1 @ sk_C_2)),
% 13.51/13.68      inference('sup-', [status(thm)], ['104', '105'])).
% 13.51/13.68  thf('125', plain, ((v1_funct_1 @ sk_C_2)),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('126', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 13.51/13.68      inference('clc', [status(thm)], ['99', '100'])).
% 13.51/13.68  thf('127', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 13.51/13.68      inference('clc', [status(thm)], ['27', '81'])).
% 13.51/13.68  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('129', plain, ((v1_relat_1 @ sk_D)),
% 13.51/13.68      inference('sup-', [status(thm)], ['111', '112'])).
% 13.51/13.68  thf('130', plain,
% 13.51/13.68      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 13.51/13.68          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 13.51/13.68        | ((sk_A) != (sk_A))
% 13.51/13.68        | ((sk_C_2) = (sk_D)))),
% 13.51/13.68      inference('demod', [status(thm)],
% 13.51/13.68                ['123', '124', '125', '126', '127', '128', '129'])).
% 13.51/13.68  thf('131', plain, (((sk_C_2) = (sk_D))),
% 13.51/13.68      inference('simplify', [status(thm)], ['130'])).
% 13.51/13.68  thf('132', plain,
% 13.51/13.68      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 13.51/13.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.51/13.68  thf('133', plain,
% 13.51/13.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 13.51/13.68         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 13.51/13.68          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 13.51/13.68      inference('simplify', [status(thm)], ['43'])).
% 13.51/13.68  thf('134', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 13.51/13.68      inference('sup-', [status(thm)], ['132', '133'])).
% 13.51/13.68  thf('135', plain, ($false),
% 13.51/13.68      inference('demod', [status(thm)], ['0', '131', '134'])).
% 13.51/13.68  
% 13.51/13.68  % SZS output end Refutation
% 13.51/13.68  
% 13.51/13.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

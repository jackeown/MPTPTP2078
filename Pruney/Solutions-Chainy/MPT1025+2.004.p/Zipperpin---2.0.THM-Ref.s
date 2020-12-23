%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XMtrRGIclQ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:43 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 193 expanded)
%              Number of leaves         :   42 (  76 expanded)
%              Depth                    :   14
%              Number of atoms          :  734 (2213 expanded)
%              Number of equality atoms :   40 (  85 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X19 @ X17 @ X18 ) @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

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

thf('15',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( r2_hidden @ ( sk_B @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_2 @ X0 )
      | ( v1_xboole_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('30',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X17 @ X18 ) @ ( k1_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('45',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('50',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('53',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X41: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X41 ) )
      | ~ ( r2_hidden @ X41 @ sk_C )
      | ~ ( m1_subset_1 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','11'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ X24 )
      | ( X25
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('61',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['56','62'])).

thf('64',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['14','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XMtrRGIclQ
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.51/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.74  % Solved by: fo/fo7.sh
% 0.51/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.74  % done 333 iterations in 0.287s
% 0.51/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.74  % SZS output start Refutation
% 0.51/0.74  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.74  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.74  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.51/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.74  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.51/0.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.74  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.74  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.51/0.74  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.74  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.51/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.51/0.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.74  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.51/0.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.51/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.74  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.51/0.74  thf(sk_E_type, type, sk_E: $i).
% 0.51/0.74  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.74  thf(t116_funct_2, conjecture,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.51/0.74         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.74       ( ![E:$i]:
% 0.51/0.74         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.51/0.74              ( ![F:$i]:
% 0.51/0.74                ( ( m1_subset_1 @ F @ A ) =>
% 0.51/0.74                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.51/0.74                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.74    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.51/0.74            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.74          ( ![E:$i]:
% 0.51/0.74            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.51/0.74                 ( ![F:$i]:
% 0.51/0.74                   ( ( m1_subset_1 @ F @ A ) =>
% 0.51/0.74                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.51/0.74                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.74    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.51/0.74  thf('0', plain,
% 0.51/0.74      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('1', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k7_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.51/0.74  thf('2', plain,
% 0.51/0.74      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.51/0.74          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.51/0.74  thf('3', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.51/0.74           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.51/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.74  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.51/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.51/0.74  thf(t143_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ C ) =>
% 0.51/0.74       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.51/0.74         ( ?[D:$i]:
% 0.51/0.74           ( ( r2_hidden @ D @ B ) & 
% 0.51/0.74             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.51/0.74             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.51/0.74  thf('5', plain,
% 0.51/0.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 0.51/0.74          | (r2_hidden @ (k4_tarski @ (sk_D @ X19 @ X17 @ X18) @ X18) @ X19)
% 0.51/0.74          | ~ (v1_relat_1 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.51/0.74  thf('6', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ sk_D_1)
% 0.51/0.74        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.51/0.74           sk_D_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.74  thf('7', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(cc2_relat_1, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( v1_relat_1 @ A ) =>
% 0.51/0.74       ( ![B:$i]:
% 0.51/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.74  thf('8', plain,
% 0.51/0.74      (![X12 : $i, X13 : $i]:
% 0.51/0.74         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.51/0.74          | (v1_relat_1 @ X12)
% 0.51/0.74          | ~ (v1_relat_1 @ X13))),
% 0.51/0.74      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.74  thf('9', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) | (v1_relat_1 @ sk_D_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.74  thf(fc6_relat_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.51/0.74  thf('10', plain,
% 0.51/0.74      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.51/0.74      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.74  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.51/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.51/0.74  thf('12', plain,
% 0.51/0.74      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.51/0.74      inference('demod', [status(thm)], ['6', '11'])).
% 0.51/0.74  thf(d1_xboole_0, axiom,
% 0.51/0.74    (![A:$i]:
% 0.51/0.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.74  thf('13', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.74  thf('14', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.51/0.74      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.74  thf(d1_funct_2, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.51/0.74             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.51/0.74         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.51/0.74             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_1, axiom,
% 0.51/0.74    (![B:$i,A:$i]:
% 0.51/0.74     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.51/0.74       ( zip_tseitin_0 @ B @ A ) ))).
% 0.51/0.74  thf('15', plain,
% 0.51/0.74      (![X33 : $i, X34 : $i]:
% 0.51/0.74         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.51/0.74  thf(t113_zfmisc_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.74       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.51/0.74  thf('16', plain,
% 0.51/0.74      (![X4 : $i, X5 : $i]:
% 0.51/0.74         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.51/0.74      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.51/0.74  thf('17', plain,
% 0.51/0.74      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.74      inference('simplify', [status(thm)], ['16'])).
% 0.51/0.74  thf('18', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.74         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.51/0.74      inference('sup+', [status(thm)], ['15', '17'])).
% 0.51/0.74  thf('19', plain,
% 0.51/0.74      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.51/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.74  thf('20', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(l3_subset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.51/0.74  thf('21', plain,
% 0.51/0.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X6 @ X7)
% 0.51/0.74          | (r2_hidden @ X6 @ X8)
% 0.51/0.74          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.51/0.74      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.51/0.74  thf('22', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.51/0.74          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.74  thf('23', plain,
% 0.51/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.51/0.74        | (r2_hidden @ (sk_B @ sk_D_1) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['19', '22'])).
% 0.51/0.74  thf('24', plain,
% 0.51/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.74  thf('25', plain,
% 0.51/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.51/0.74        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.51/0.74  thf('26', plain,
% 0.51/0.74      (![X0 : $i]:
% 0.51/0.74         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.51/0.74          | (zip_tseitin_0 @ sk_B_2 @ X0)
% 0.51/0.74          | (v1_xboole_0 @ sk_D_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['18', '25'])).
% 0.51/0.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.51/0.74  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.74  thf('28', plain,
% 0.51/0.74      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_2 @ X0) | (v1_xboole_0 @ sk_D_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['26', '27'])).
% 0.51/0.74  thf('29', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_3, axiom,
% 0.51/0.74    (![C:$i,B:$i,A:$i]:
% 0.51/0.74     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.51/0.74       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.51/0.74  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.51/0.74  thf(zf_stmt_5, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.51/0.74         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.51/0.74           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.51/0.74             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.51/0.74  thf('30', plain,
% 0.51/0.74      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.51/0.74         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.51/0.74          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.51/0.74          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.51/0.74  thf('31', plain,
% 0.51/0.74      (((zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A)
% 0.51/0.74        | ~ (zip_tseitin_0 @ sk_B_2 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.51/0.74  thf('32', plain,
% 0.51/0.74      (((v1_xboole_0 @ sk_D_1) | (zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A))),
% 0.51/0.74      inference('sup-', [status(thm)], ['28', '31'])).
% 0.51/0.74  thf('33', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_2)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('34', plain,
% 0.51/0.74      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.51/0.74         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.51/0.74          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.51/0.74          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.74  thf('35', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A)
% 0.51/0.74        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_1)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.74  thf('36', plain,
% 0.51/0.74      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.74       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.74  thf('37', plain,
% 0.51/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.51/0.74         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.51/0.74          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.51/0.74      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.74  thf('38', plain,
% 0.51/0.74      (((k1_relset_1 @ sk_A @ sk_B_2 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.74  thf('39', plain,
% 0.51/0.74      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_2 @ sk_A)
% 0.51/0.74        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.51/0.74      inference('demod', [status(thm)], ['35', '38'])).
% 0.51/0.74  thf('40', plain,
% 0.51/0.74      (((v1_xboole_0 @ sk_D_1) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['32', '39'])).
% 0.51/0.74  thf('41', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.51/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.51/0.74  thf('42', plain,
% 0.51/0.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 0.51/0.74          | (r2_hidden @ (sk_D @ X19 @ X17 @ X18) @ (k1_relat_1 @ X19))
% 0.51/0.74          | ~ (v1_relat_1 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.51/0.74  thf('43', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ sk_D_1)
% 0.51/0.74        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.51/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.51/0.74  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 0.51/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.51/0.74  thf('45', plain,
% 0.51/0.74      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.51/0.74      inference('demod', [status(thm)], ['43', '44'])).
% 0.51/0.74  thf(t1_subset, axiom,
% 0.51/0.74    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.51/0.74  thf('46', plain,
% 0.51/0.74      (![X9 : $i, X10 : $i]:
% 0.51/0.74         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.51/0.74      inference('cnf', [status(esa)], [t1_subset])).
% 0.51/0.74  thf('47', plain,
% 0.51/0.74      ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.51/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.51/0.74  thf('48', plain,
% 0.51/0.74      (((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.51/0.74        | (v1_xboole_0 @ sk_D_1))),
% 0.51/0.74      inference('sup+', [status(thm)], ['40', '47'])).
% 0.51/0.74  thf('49', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.51/0.74      inference('demod', [status(thm)], ['0', '3'])).
% 0.51/0.74  thf('50', plain,
% 0.51/0.74      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.74         (~ (r2_hidden @ X18 @ (k9_relat_1 @ X19 @ X17))
% 0.51/0.74          | (r2_hidden @ (sk_D @ X19 @ X17 @ X18) @ X17)
% 0.51/0.74          | ~ (v1_relat_1 @ X19))),
% 0.51/0.74      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.51/0.74  thf('51', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ sk_D_1)
% 0.51/0.74        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.51/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.51/0.74  thf('52', plain, ((v1_relat_1 @ sk_D_1)),
% 0.51/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.51/0.74  thf('53', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.51/0.74      inference('demod', [status(thm)], ['51', '52'])).
% 0.51/0.74  thf('54', plain,
% 0.51/0.74      (![X41 : $i]:
% 0.51/0.74         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X41))
% 0.51/0.74          | ~ (r2_hidden @ X41 @ sk_C)
% 0.51/0.74          | ~ (m1_subset_1 @ X41 @ sk_A))),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('55', plain,
% 0.51/0.74      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.51/0.74        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.51/0.74  thf('56', plain,
% 0.51/0.74      (((v1_xboole_0 @ sk_D_1)
% 0.51/0.74        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['48', '55'])).
% 0.51/0.74  thf('57', plain,
% 0.51/0.74      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.51/0.74      inference('demod', [status(thm)], ['6', '11'])).
% 0.51/0.74  thf(t8_funct_1, axiom,
% 0.51/0.74    (![A:$i,B:$i,C:$i]:
% 0.51/0.74     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.51/0.74       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.51/0.74         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.51/0.74           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.51/0.74  thf('58', plain,
% 0.51/0.74      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.51/0.74         (~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ X24)
% 0.51/0.74          | ((X25) = (k1_funct_1 @ X24 @ X23))
% 0.51/0.74          | ~ (v1_funct_1 @ X24)
% 0.51/0.74          | ~ (v1_relat_1 @ X24))),
% 0.51/0.74      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.51/0.74  thf('59', plain,
% 0.51/0.74      ((~ (v1_relat_1 @ sk_D_1)
% 0.51/0.74        | ~ (v1_funct_1 @ sk_D_1)
% 0.51/0.74        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.51/0.74      inference('sup-', [status(thm)], ['57', '58'])).
% 0.51/0.74  thf('60', plain, ((v1_relat_1 @ sk_D_1)),
% 0.51/0.74      inference('demod', [status(thm)], ['9', '10'])).
% 0.51/0.74  thf('61', plain, ((v1_funct_1 @ sk_D_1)),
% 0.51/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.74  thf('62', plain,
% 0.51/0.74      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.51/0.74      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.51/0.74  thf('63', plain, (((v1_xboole_0 @ sk_D_1) | ((sk_E) != (sk_E)))),
% 0.51/0.74      inference('demod', [status(thm)], ['56', '62'])).
% 0.51/0.74  thf('64', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.51/0.74      inference('simplify', [status(thm)], ['63'])).
% 0.51/0.74  thf('65', plain, ($false), inference('demod', [status(thm)], ['14', '64'])).
% 0.51/0.74  
% 0.51/0.74  % SZS output end Refutation
% 0.51/0.74  
% 0.58/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gaMQzHzCj9

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:47 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 834 expanded)
%              Number of leaves         :   40 ( 260 expanded)
%              Depth                    :   18
%              Number of atoms          :  840 (11988 expanded)
%              Number of equality atoms :   57 ( 493 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 )
        = ( k9_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X27 @ X25 ) @ X25 )
      | ( ( k1_relset_1 @ X25 @ X26 @ X27 )
        = X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('15',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ~ ( r1_tarski @ sk_A @ ( sk_D_1 @ sk_D_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('23',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('25',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('42',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_C ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X38: $i] :
      ( ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X38 ) )
      | ~ ( r2_hidden @ X38 @ sk_C )
      | ~ ( m1_subset_1 @ X38 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_A )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['47','48'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('53',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_E_1
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_A )
    | ( sk_E_1 != sk_E_1 ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('56',plain,(
    ~ ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['37','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','57'])).

thf('59',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35 != k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('60',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ k1_xboole_0 )
      | ( X37 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['37','56'])).

thf('64',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['47','48'])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('68',plain,(
    ~ ( r1_tarski @ sk_D_2 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ sk_E_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['69','70'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['21','71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['12','75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gaMQzHzCj9
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.82  % Solved by: fo/fo7.sh
% 0.60/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.82  % done 308 iterations in 0.373s
% 0.60/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.82  % SZS output start Refutation
% 0.60/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.82  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.82  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.60/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.82  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.82  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.60/0.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.82  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.60/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.82  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.60/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.82  thf(t116_funct_2, conjecture,
% 0.60/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.82     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.82       ( ![E:$i]:
% 0.60/0.82         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.82              ( ![F:$i]:
% 0.60/0.82                ( ( m1_subset_1 @ F @ A ) =>
% 0.60/0.82                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.60/0.82                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.82        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.82            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.82          ( ![E:$i]:
% 0.60/0.82            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.82                 ( ![F:$i]:
% 0.60/0.82                   ( ( m1_subset_1 @ F @ A ) =>
% 0.60/0.82                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.60/0.82                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.82    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.60/0.82  thf('0', plain,
% 0.60/0.82      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('1', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(redefinition_k7_relset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.82       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.60/0.82  thf('2', plain,
% 0.60/0.82      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.82         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.60/0.82          | ((k7_relset_1 @ X22 @ X23 @ X21 @ X24) = (k9_relat_1 @ X21 @ X24)))),
% 0.60/0.82      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.82  thf('3', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.60/0.82           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.82  thf('4', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.82  thf(t143_relat_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( v1_relat_1 @ C ) =>
% 0.60/0.82       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.60/0.82         ( ?[D:$i]:
% 0.60/0.82           ( ( r2_hidden @ D @ B ) & 
% 0.60/0.82             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.60/0.82             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.60/0.82  thf('5', plain,
% 0.60/0.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.60/0.82          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.60/0.82          | ~ (v1_relat_1 @ X9))),
% 0.60/0.82      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.82  thf('6', plain,
% 0.60/0.82      ((~ (v1_relat_1 @ sk_D_2)
% 0.60/0.82        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.82  thf('7', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(cc1_relset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.82       ( v1_relat_1 @ C ) ))).
% 0.60/0.82  thf('8', plain,
% 0.60/0.82      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.82         ((v1_relat_1 @ X15)
% 0.60/0.82          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.60/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.82  thf('9', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.82  thf('10', plain,
% 0.60/0.82      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.60/0.82      inference('demod', [status(thm)], ['6', '9'])).
% 0.60/0.82  thf(t7_ordinal1, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.82  thf('11', plain,
% 0.60/0.82      (![X13 : $i, X14 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.60/0.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.82  thf('12', plain,
% 0.60/0.82      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.82  thf('13', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t22_relset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.60/0.82       ( ( ![D:$i]:
% 0.60/0.82           ( ~( ( r2_hidden @ D @ B ) & 
% 0.60/0.82                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.60/0.82         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.60/0.82  thf('14', plain,
% 0.60/0.82      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.82         ((r2_hidden @ (sk_D_1 @ X27 @ X25) @ X25)
% 0.60/0.82          | ((k1_relset_1 @ X25 @ X26 @ X27) = (X25))
% 0.60/0.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.60/0.82      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.60/0.82  thf('15', plain,
% 0.60/0.82      ((((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (sk_A))
% 0.60/0.82        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.60/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.82  thf('16', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.82  thf('17', plain,
% 0.60/0.82      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.60/0.82         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.60/0.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.60/0.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.82  thf('18', plain,
% 0.60/0.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.60/0.82      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.82  thf('19', plain,
% 0.60/0.82      ((((k1_relat_1 @ sk_D_2) = (sk_A))
% 0.60/0.82        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.60/0.82      inference('demod', [status(thm)], ['15', '18'])).
% 0.60/0.82  thf('20', plain,
% 0.60/0.82      (![X13 : $i, X14 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.60/0.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.82  thf('21', plain,
% 0.60/0.82      ((((k1_relat_1 @ sk_D_2) = (sk_A))
% 0.60/0.82        | ~ (r1_tarski @ sk_A @ (sk_D_1 @ sk_D_2 @ sk_A)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.82  thf('22', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(d1_funct_2, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_1, axiom,
% 0.60/0.82    (![B:$i,A:$i]:
% 0.60/0.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.82       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.82  thf('23', plain,
% 0.60/0.82      (![X30 : $i, X31 : $i]:
% 0.60/0.82         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.82  thf('24', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.82  thf(zf_stmt_3, axiom,
% 0.60/0.82    (![C:$i,B:$i,A:$i]:
% 0.60/0.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.82  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.82  thf(zf_stmt_5, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.82  thf('25', plain,
% 0.60/0.82      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.60/0.82         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.60/0.82          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.60/0.82          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.82  thf('26', plain,
% 0.60/0.82      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.82        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.60/0.82      inference('sup-', [status(thm)], ['24', '25'])).
% 0.60/0.82  thf('27', plain,
% 0.60/0.82      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.60/0.82      inference('sup-', [status(thm)], ['23', '26'])).
% 0.60/0.82  thf('28', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('29', plain,
% 0.60/0.82      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.60/0.82         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.60/0.82          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.60/0.82          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.82  thf('30', plain,
% 0.60/0.82      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.82  thf('31', plain,
% 0.60/0.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.60/0.82      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.82  thf('32', plain,
% 0.60/0.82      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.82        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.82      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.82  thf('33', plain,
% 0.60/0.82      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['27', '32'])).
% 0.60/0.82  thf('34', plain,
% 0.60/0.82      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.60/0.82      inference('demod', [status(thm)], ['6', '9'])).
% 0.60/0.82  thf(t1_subset, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.60/0.82  thf('35', plain,
% 0.60/0.82      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.60/0.82      inference('cnf', [status(esa)], [t1_subset])).
% 0.60/0.82  thf('36', plain,
% 0.60/0.82      ((m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.60/0.82      inference('sup-', [status(thm)], ['34', '35'])).
% 0.60/0.82  thf('37', plain,
% 0.60/0.82      (((m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_A)
% 0.60/0.82        | ((sk_B) = (k1_xboole_0)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['33', '36'])).
% 0.60/0.82  thf('38', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.82  thf('39', plain,
% 0.60/0.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.60/0.82          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 0.60/0.82          | ~ (v1_relat_1 @ X9))),
% 0.60/0.82      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.82  thf('40', plain,
% 0.60/0.82      ((~ (v1_relat_1 @ sk_D_2)
% 0.60/0.82        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C))),
% 0.60/0.82      inference('sup-', [status(thm)], ['38', '39'])).
% 0.60/0.82  thf('41', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.82  thf('42', plain, ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_C)),
% 0.60/0.82      inference('demod', [status(thm)], ['40', '41'])).
% 0.60/0.82  thf('43', plain,
% 0.60/0.82      (![X38 : $i]:
% 0.60/0.82         (((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X38))
% 0.60/0.82          | ~ (r2_hidden @ X38 @ sk_C)
% 0.60/0.82          | ~ (m1_subset_1 @ X38 @ sk_A))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('44', plain,
% 0.60/0.82      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_A)
% 0.60/0.82        | ((sk_E_1) != (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1))))),
% 0.60/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.82  thf('45', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.82  thf('46', plain,
% 0.60/0.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.60/0.82          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 0.60/0.82          | ~ (v1_relat_1 @ X9))),
% 0.60/0.82      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.82  thf('47', plain,
% 0.60/0.82      ((~ (v1_relat_1 @ sk_D_2)
% 0.60/0.82        | (r2_hidden @ 
% 0.60/0.82           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ sk_D_2))),
% 0.60/0.82      inference('sup-', [status(thm)], ['45', '46'])).
% 0.60/0.82  thf('48', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.82  thf('49', plain,
% 0.60/0.82      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ 
% 0.60/0.82        sk_D_2)),
% 0.60/0.82      inference('demod', [status(thm)], ['47', '48'])).
% 0.60/0.82  thf(t8_funct_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.60/0.82       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.60/0.82         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.60/0.82           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.60/0.82  thf('50', plain,
% 0.60/0.82      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.82         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.60/0.82          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.60/0.82          | ~ (v1_funct_1 @ X11)
% 0.60/0.82          | ~ (v1_relat_1 @ X11))),
% 0.60/0.82      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.60/0.82  thf('51', plain,
% 0.60/0.82      ((~ (v1_relat_1 @ sk_D_2)
% 0.60/0.82        | ~ (v1_funct_1 @ sk_D_2)
% 0.60/0.82        | ((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1))))),
% 0.60/0.82      inference('sup-', [status(thm)], ['49', '50'])).
% 0.60/0.82  thf('52', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.82  thf('53', plain, ((v1_funct_1 @ sk_D_2)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('54', plain,
% 0.60/0.82      (((sk_E_1) = (k1_funct_1 @ sk_D_2 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1)))),
% 0.60/0.82      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.60/0.82  thf('55', plain,
% 0.60/0.82      ((~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_A)
% 0.60/0.82        | ((sk_E_1) != (sk_E_1)))),
% 0.60/0.82      inference('demod', [status(thm)], ['44', '54'])).
% 0.60/0.82  thf('56', plain, (~ (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_A)),
% 0.60/0.82      inference('simplify', [status(thm)], ['55'])).
% 0.60/0.82  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.82      inference('clc', [status(thm)], ['37', '56'])).
% 0.60/0.82  thf('58', plain,
% 0.60/0.82      ((m1_subset_1 @ sk_D_2 @ 
% 0.60/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.60/0.82      inference('demod', [status(thm)], ['22', '57'])).
% 0.60/0.82  thf('59', plain,
% 0.60/0.82      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.60/0.82         (((X35) != (k1_xboole_0))
% 0.60/0.82          | ((X36) = (k1_xboole_0))
% 0.60/0.82          | ((X37) = (k1_xboole_0))
% 0.60/0.82          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.60/0.82          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.82  thf('60', plain,
% 0.60/0.82      (![X36 : $i, X37 : $i]:
% 0.60/0.82         (~ (m1_subset_1 @ X37 @ 
% 0.60/0.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ k1_xboole_0)))
% 0.60/0.82          | ~ (v1_funct_2 @ X37 @ X36 @ k1_xboole_0)
% 0.60/0.82          | ((X37) = (k1_xboole_0))
% 0.60/0.82          | ((X36) = (k1_xboole_0)))),
% 0.60/0.82      inference('simplify', [status(thm)], ['59'])).
% 0.60/0.82  thf('61', plain,
% 0.60/0.82      ((((sk_A) = (k1_xboole_0))
% 0.60/0.82        | ((sk_D_2) = (k1_xboole_0))
% 0.60/0.82        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['58', '60'])).
% 0.60/0.82  thf('62', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf('63', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.82      inference('clc', [status(thm)], ['37', '56'])).
% 0.60/0.82  thf('64', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.60/0.82      inference('demod', [status(thm)], ['62', '63'])).
% 0.60/0.82  thf('65', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.60/0.82      inference('demod', [status(thm)], ['61', '64'])).
% 0.60/0.82  thf('66', plain,
% 0.60/0.82      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1) @ 
% 0.60/0.82        sk_D_2)),
% 0.60/0.82      inference('demod', [status(thm)], ['47', '48'])).
% 0.60/0.82  thf('67', plain,
% 0.60/0.82      (![X13 : $i, X14 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 0.60/0.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.82  thf('68', plain,
% 0.60/0.82      (~ (r1_tarski @ sk_D_2 @ 
% 0.60/0.82          (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['66', '67'])).
% 0.60/0.82  thf('69', plain,
% 0.60/0.82      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.60/0.82           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ sk_E_1))
% 0.60/0.82        | ((sk_A) = (k1_xboole_0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['65', '68'])).
% 0.60/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.82  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.60/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.82  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.82      inference('demod', [status(thm)], ['69', '70'])).
% 0.60/0.82  thf('72', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.82      inference('demod', [status(thm)], ['69', '70'])).
% 0.60/0.82  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.82      inference('demod', [status(thm)], ['69', '70'])).
% 0.60/0.82  thf('74', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.60/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.82  thf('75', plain, (((k1_relat_1 @ sk_D_2) = (k1_xboole_0))),
% 0.60/0.82      inference('demod', [status(thm)], ['21', '71', '72', '73', '74'])).
% 0.60/0.82  thf('76', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.60/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.82  thf('77', plain, ($false),
% 0.60/0.82      inference('demod', [status(thm)], ['12', '75', '76'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

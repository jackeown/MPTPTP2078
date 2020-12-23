%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LC8mEDb4a6

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:35 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  122 (1136 expanded)
%              Number of leaves         :   38 ( 351 expanded)
%              Depth                    :   20
%              Number of atoms          :  828 (15656 expanded)
%              Number of equality atoms :   59 ( 649 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('14',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X35: $i] :
      ( ~ ( r2_hidden @ X35 @ sk_A )
      | ~ ( r2_hidden @ X35 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('37',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X12 @ X14 ) @ X13 )
      | ( X14
        = ( k1_funct_1 @ X13 @ X12 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('47',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['32','42','47'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['21','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('53',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 != k1_xboole_0 )
      | ( X33 = k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('55',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ k1_xboole_0 )
      | ( X34 = k1_xboole_0 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('59',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('62',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ~ ( r1_tarski @ sk_D_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['50','66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('71',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('73',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('75',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    ! [X27: $i] :
      ( zip_tseitin_0 @ X27 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['77'])).

thf('79',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['68','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['14','80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LC8mEDb4a6
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.65/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.65/0.84  % Solved by: fo/fo7.sh
% 0.65/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.84  % done 231 iterations in 0.346s
% 0.65/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.65/0.84  % SZS output start Refutation
% 0.65/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.84  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.65/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.84  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.65/0.84  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.65/0.84  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.65/0.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.65/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.65/0.84  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.65/0.84  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.65/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.65/0.84  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.65/0.84  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.65/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.65/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.65/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.84  thf(sk_E_type, type, sk_E: $i).
% 0.65/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.65/0.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.65/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.65/0.84  thf(t115_funct_2, conjecture,
% 0.65/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.65/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.84       ( ![E:$i]:
% 0.65/0.84         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.65/0.84              ( ![F:$i]:
% 0.65/0.84                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.65/0.84                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.65/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.84    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.65/0.84            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.65/0.84          ( ![E:$i]:
% 0.65/0.84            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.65/0.84                 ( ![F:$i]:
% 0.65/0.84                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.65/0.84                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.65/0.84    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.65/0.84  thf('0', plain,
% 0.65/0.84      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('1', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf(redefinition_k7_relset_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.84       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.65/0.84  thf('2', plain,
% 0.65/0.84      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.65/0.84          | ((k7_relset_1 @ X24 @ X25 @ X23 @ X26) = (k9_relat_1 @ X23 @ X26)))),
% 0.65/0.84      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.65/0.84  thf('3', plain,
% 0.65/0.84      (![X0 : $i]:
% 0.65/0.84         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.65/0.84           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.65/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.65/0.84  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.65/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.65/0.84  thf(t143_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ C ) =>
% 0.65/0.84       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.65/0.84         ( ?[D:$i]:
% 0.65/0.84           ( ( r2_hidden @ D @ B ) & 
% 0.65/0.84             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.65/0.84             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.65/0.84  thf('5', plain,
% 0.65/0.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.65/0.84         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.65/0.84          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.65/0.84          | ~ (v1_relat_1 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.65/0.84  thf('6', plain,
% 0.65/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.65/0.84        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.65/0.84  thf('7', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf(cc2_relat_1, axiom,
% 0.65/0.84    (![A:$i]:
% 0.65/0.84     ( ( v1_relat_1 @ A ) =>
% 0.65/0.84       ( ![B:$i]:
% 0.65/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.65/0.84  thf('8', plain,
% 0.65/0.84      (![X4 : $i, X5 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.65/0.84          | (v1_relat_1 @ X4)
% 0.65/0.84          | ~ (v1_relat_1 @ X5))),
% 0.65/0.84      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.65/0.84  thf('9', plain,
% 0.65/0.84      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.65/0.84      inference('sup-', [status(thm)], ['7', '8'])).
% 0.65/0.84  thf(fc6_relat_1, axiom,
% 0.65/0.84    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.65/0.84  thf('10', plain,
% 0.65/0.84      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.65/0.84      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.65/0.84  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.65/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.65/0.84  thf('12', plain,
% 0.65/0.84      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.65/0.84      inference('demod', [status(thm)], ['6', '11'])).
% 0.65/0.84  thf(t7_ordinal1, axiom,
% 0.65/0.84    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.65/0.84  thf('13', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.65/0.84      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.65/0.84  thf('14', plain,
% 0.65/0.84      (~ (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (sk_D @ sk_D_1 @ sk_C @ sk_E))),
% 0.65/0.84      inference('sup-', [status(thm)], ['12', '13'])).
% 0.65/0.84  thf('15', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf(d1_funct_2, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.84       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.65/0.84           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.65/0.84             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.65/0.84         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.65/0.84           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.65/0.84             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.65/0.84  thf(zf_stmt_1, axiom,
% 0.65/0.84    (![C:$i,B:$i,A:$i]:
% 0.65/0.84     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.65/0.84       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.65/0.84  thf('16', plain,
% 0.65/0.84      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.65/0.84         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.65/0.84          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.65/0.84          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.65/0.84  thf('17', plain,
% 0.65/0.84      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.65/0.84        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['15', '16'])).
% 0.65/0.84  thf('18', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf(redefinition_k1_relset_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.84       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.65/0.84  thf('19', plain,
% 0.65/0.84      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.65/0.84         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.65/0.84          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.65/0.84      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.65/0.84  thf('20', plain,
% 0.65/0.84      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.65/0.84      inference('sup-', [status(thm)], ['18', '19'])).
% 0.65/0.84  thf('21', plain,
% 0.65/0.84      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.65/0.84        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.65/0.84      inference('demod', [status(thm)], ['17', '20'])).
% 0.65/0.84  thf(zf_stmt_2, axiom,
% 0.65/0.84    (![B:$i,A:$i]:
% 0.65/0.84     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.65/0.84       ( zip_tseitin_0 @ B @ A ) ))).
% 0.65/0.84  thf('22', plain,
% 0.65/0.84      (![X27 : $i, X28 : $i]:
% 0.65/0.84         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.65/0.84  thf('23', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.65/0.84  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.65/0.84  thf(zf_stmt_5, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.65/0.84       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.65/0.84         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.65/0.84           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.65/0.84             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.65/0.84  thf('24', plain,
% 0.65/0.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.65/0.84         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.65/0.84          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.65/0.84          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.65/0.84  thf('25', plain,
% 0.65/0.84      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.65/0.84        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.65/0.84      inference('sup-', [status(thm)], ['23', '24'])).
% 0.65/0.84  thf('26', plain,
% 0.65/0.84      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.65/0.84      inference('sup-', [status(thm)], ['22', '25'])).
% 0.65/0.84  thf('27', plain,
% 0.65/0.84      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.65/0.84        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.65/0.84      inference('demod', [status(thm)], ['17', '20'])).
% 0.65/0.84  thf('28', plain,
% 0.65/0.84      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.65/0.84  thf('29', plain,
% 0.65/0.84      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.65/0.84      inference('demod', [status(thm)], ['6', '11'])).
% 0.65/0.84  thf('30', plain,
% 0.65/0.84      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.65/0.84        | ((sk_B) = (k1_xboole_0)))),
% 0.65/0.84      inference('sup+', [status(thm)], ['28', '29'])).
% 0.65/0.84  thf('31', plain,
% 0.65/0.84      (![X35 : $i]:
% 0.65/0.84         (~ (r2_hidden @ X35 @ sk_A)
% 0.65/0.84          | ~ (r2_hidden @ X35 @ sk_C)
% 0.65/0.84          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X35)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('32', plain,
% 0.65/0.84      ((((sk_B) = (k1_xboole_0))
% 0.65/0.84        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.65/0.84        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.65/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.65/0.84  thf('33', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.65/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.65/0.84  thf('34', plain,
% 0.65/0.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.65/0.84         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.65/0.84          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X9 @ X10) @ X10) @ X11)
% 0.65/0.84          | ~ (v1_relat_1 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.65/0.84  thf('35', plain,
% 0.65/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.65/0.84        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.65/0.84           sk_D_1))),
% 0.65/0.84      inference('sup-', [status(thm)], ['33', '34'])).
% 0.65/0.84  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 0.65/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.65/0.84  thf('37', plain,
% 0.65/0.84      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.65/0.84      inference('demod', [status(thm)], ['35', '36'])).
% 0.65/0.84  thf(t8_funct_1, axiom,
% 0.65/0.84    (![A:$i,B:$i,C:$i]:
% 0.65/0.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.65/0.84       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.65/0.84         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.65/0.84           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.65/0.84  thf('38', plain,
% 0.65/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.84         (~ (r2_hidden @ (k4_tarski @ X12 @ X14) @ X13)
% 0.65/0.84          | ((X14) = (k1_funct_1 @ X13 @ X12))
% 0.65/0.84          | ~ (v1_funct_1 @ X13)
% 0.65/0.84          | ~ (v1_relat_1 @ X13))),
% 0.65/0.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.65/0.84  thf('39', plain,
% 0.65/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.65/0.84        | ~ (v1_funct_1 @ sk_D_1)
% 0.65/0.84        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.65/0.84      inference('sup-', [status(thm)], ['37', '38'])).
% 0.65/0.84  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.65/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.65/0.84  thf('41', plain, ((v1_funct_1 @ sk_D_1)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('42', plain,
% 0.65/0.84      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.65/0.84      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.65/0.84  thf('43', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.65/0.84      inference('demod', [status(thm)], ['0', '3'])).
% 0.65/0.84  thf('44', plain,
% 0.65/0.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.65/0.84         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.65/0.84          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.65/0.84          | ~ (v1_relat_1 @ X11))),
% 0.65/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.65/0.84  thf('45', plain,
% 0.65/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.65/0.84        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.65/0.84      inference('sup-', [status(thm)], ['43', '44'])).
% 0.65/0.84  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.65/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.65/0.84  thf('47', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.65/0.84      inference('demod', [status(thm)], ['45', '46'])).
% 0.65/0.84  thf('48', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.65/0.84      inference('demod', [status(thm)], ['32', '42', '47'])).
% 0.65/0.84  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 0.65/0.84      inference('simplify', [status(thm)], ['48'])).
% 0.65/0.84  thf('50', plain,
% 0.65/0.84      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A)
% 0.65/0.84        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.65/0.84      inference('demod', [status(thm)], ['21', '49'])).
% 0.65/0.84  thf('51', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('52', plain, (((sk_B) = (k1_xboole_0))),
% 0.65/0.84      inference('simplify', [status(thm)], ['48'])).
% 0.65/0.84  thf('53', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ 
% 0.65/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['51', '52'])).
% 0.65/0.84  thf('54', plain,
% 0.65/0.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.65/0.84         (((X32) != (k1_xboole_0))
% 0.65/0.84          | ((X33) = (k1_xboole_0))
% 0.65/0.84          | ((X34) = (k1_xboole_0))
% 0.65/0.84          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 0.65/0.84          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.65/0.84  thf('55', plain,
% 0.65/0.84      (![X33 : $i, X34 : $i]:
% 0.65/0.84         (~ (m1_subset_1 @ X34 @ 
% 0.65/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ k1_xboole_0)))
% 0.65/0.84          | ~ (v1_funct_2 @ X34 @ X33 @ k1_xboole_0)
% 0.65/0.84          | ((X34) = (k1_xboole_0))
% 0.65/0.84          | ((X33) = (k1_xboole_0)))),
% 0.65/0.84      inference('simplify', [status(thm)], ['54'])).
% 0.65/0.84  thf('56', plain,
% 0.65/0.84      ((((sk_A) = (k1_xboole_0))
% 0.65/0.84        | ((sk_D_1) = (k1_xboole_0))
% 0.65/0.84        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0))),
% 0.65/0.84      inference('sup-', [status(thm)], ['53', '55'])).
% 0.65/0.84  thf('57', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.84  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 0.65/0.84      inference('simplify', [status(thm)], ['48'])).
% 0.65/0.84  thf('59', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.65/0.84      inference('demod', [status(thm)], ['57', '58'])).
% 0.65/0.84  thf('60', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['56', '59'])).
% 0.65/0.84  thf('61', plain,
% 0.65/0.84      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.65/0.84      inference('demod', [status(thm)], ['35', '36'])).
% 0.65/0.84  thf('62', plain,
% 0.65/0.84      (![X15 : $i, X16 : $i]:
% 0.65/0.84         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.65/0.84      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.65/0.84  thf('63', plain,
% 0.65/0.84      (~ (r1_tarski @ sk_D_1 @ 
% 0.65/0.84          (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E))),
% 0.65/0.84      inference('sup-', [status(thm)], ['61', '62'])).
% 0.65/0.84  thf('64', plain,
% 0.65/0.84      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.65/0.84           (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E))
% 0.65/0.84        | ((sk_A) = (k1_xboole_0)))),
% 0.65/0.84      inference('sup-', [status(thm)], ['60', '63'])).
% 0.65/0.84  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.65/0.84  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.65/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.65/0.84  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['64', '65'])).
% 0.65/0.84  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['64', '65'])).
% 0.65/0.84  thf('68', plain,
% 0.65/0.84      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.65/0.84        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.65/0.84      inference('demod', [status(thm)], ['50', '66', '67'])).
% 0.65/0.84  thf('69', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ 
% 0.65/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['51', '52'])).
% 0.65/0.84  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.65/0.84      inference('demod', [status(thm)], ['64', '65'])).
% 0.65/0.84  thf('71', plain,
% 0.65/0.84      ((m1_subset_1 @ sk_D_1 @ 
% 0.65/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.65/0.84      inference('demod', [status(thm)], ['69', '70'])).
% 0.65/0.84  thf('72', plain,
% 0.65/0.84      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.65/0.84         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.65/0.84          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.65/0.84          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.65/0.84  thf('73', plain,
% 0.65/0.84      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.65/0.84        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.65/0.84      inference('sup-', [status(thm)], ['71', '72'])).
% 0.65/0.84  thf('74', plain,
% 0.65/0.84      (![X27 : $i, X28 : $i]:
% 0.65/0.84         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.65/0.84  thf('75', plain,
% 0.65/0.84      (![X27 : $i, X28 : $i]:
% 0.65/0.84         ((zip_tseitin_0 @ X27 @ X28) | ((X28) != (k1_xboole_0)))),
% 0.65/0.84      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.65/0.84  thf('76', plain, (![X27 : $i]: (zip_tseitin_0 @ X27 @ k1_xboole_0)),
% 0.65/0.84      inference('simplify', [status(thm)], ['75'])).
% 0.65/0.84  thf('77', plain,
% 0.65/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.65/0.84         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.65/0.84      inference('sup+', [status(thm)], ['74', '76'])).
% 0.65/0.84  thf('78', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.65/0.84      inference('eq_fact', [status(thm)], ['77'])).
% 0.65/0.84  thf('79', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.65/0.84      inference('demod', [status(thm)], ['73', '78'])).
% 0.65/0.84  thf('80', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.65/0.84      inference('demod', [status(thm)], ['68', '79'])).
% 0.65/0.84  thf('81', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.65/0.84      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.65/0.84  thf('82', plain, ($false),
% 0.65/0.84      inference('demod', [status(thm)], ['14', '80', '81'])).
% 0.65/0.84  
% 0.65/0.84  % SZS output end Refutation
% 0.65/0.84  
% 0.65/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

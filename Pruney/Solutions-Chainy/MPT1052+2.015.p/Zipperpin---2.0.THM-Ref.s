%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4COBpN7cZr

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 373 expanded)
%              Number of leaves         :   42 ( 129 expanded)
%              Depth                    :   23
%              Number of atoms          :  737 (3309 expanded)
%              Number of equality atoms :   78 ( 250 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('3',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) )
        = X18 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('7',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_hidden @ X34 @ ( k1_funct_2 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('21',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('35',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('37',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','35','36'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['5','37','38','39'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['4','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

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

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('47',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('48',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X34 @ ( k1_funct_2 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('52',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['4','42'])).

thf('61',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','61','63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['43','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('70',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4COBpN7cZr
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 119 iterations in 0.096s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(l13_xboole_0, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.55      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(t169_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.20/0.55         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.55           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.55        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.55          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.20/0.55            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.55              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.20/0.55        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.20/0.55         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf(t195_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.55          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.55               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i]:
% 0.20/0.55         (((X17) = (k1_xboole_0))
% 0.20/0.55          | ((k2_relat_1 @ (k2_zfmisc_1 @ X17 @ X18)) = (X18))
% 0.20/0.55          | ((X18) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.55  thf('7', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t121_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.20/0.55       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.20/0.55          | ~ (r2_hidden @ X34 @ (k1_funct_2 @ X35 @ X36)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf(t3_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i]:
% 0.20/0.55         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('11', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf(t25_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( v1_relat_1 @ B ) =>
% 0.20/0.55           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.55             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.55               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X19)
% 0.20/0.55          | (r1_tarski @ (k2_relat_1 @ X20) @ (k2_relat_1 @ X19))
% 0.20/0.55          | ~ (r1_tarski @ X20 @ X19)
% 0.20/0.55          | ~ (v1_relat_1 @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.55        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.55           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.20/0.55        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.55  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(fc6_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.55        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)
% 0.20/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['6', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf(fc3_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.20/0.55       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X32 : $i, X33 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X32)
% 0.20/0.55          | ~ (v1_xboole_0 @ X33)
% 0.20/0.55          | (v1_xboole_0 @ (k1_funct_2 @ X32 @ X33)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.20/0.55  thf('21', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(d1_xboole_0, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.55  thf('23', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.55  thf('24', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.55         | ((sk_A) = (k1_xboole_0))
% 0.20/0.55         | (v1_xboole_0 @ sk_A)))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '24'])).
% 0.20/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.55  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_A)))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.55  thf('30', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.55  thf(l32_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X4 : $i, X6 : $i]:
% 0.20/0.55         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      ((((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.20/0.55          = (k1_xboole_0)))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['29', '32'])).
% 0.20/0.55  thf(t113_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.20/0.55          | ((X10) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.55  thf(t3_boole, axiom,
% 0.20/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.55  thf('36', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      ((((sk_C) = (k1_xboole_0)))
% 0.20/0.55         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['33', '35', '36'])).
% 0.20/0.55  thf(t60_relat_1, axiom,
% 0.20/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('38', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('39', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('40', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '37', '38', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (~ (((k1_relat_1 @ sk_C) = (sk_A))) | 
% 0.20/0.55       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('42', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.55  thf('43', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['4', '42'])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.55  thf(d1_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.55             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.55         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.55             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, axiom,
% 0.20/0.55    (![B:$i,A:$i]:
% 0.20/0.55     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.55       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      (![X24 : $i, X25 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_3, axiom,
% 0.20/0.55    (![C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.55       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_5, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.55           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.55         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.20/0.55          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.20/0.55          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.20/0.55        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.55  thf('49', plain,
% 0.20/0.55      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.55  thf('50', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.55         ((v1_funct_2 @ X34 @ X35 @ X36)
% 0.20/0.55          | ~ (r2_hidden @ X34 @ (k1_funct_2 @ X35 @ X36)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.20/0.55  thf('52', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.55         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.20/0.55          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.20/0.55          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.20/0.55        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.55         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.20/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.20/0.55        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['54', '57'])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['49', '58'])).
% 0.20/0.55  thf('60', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['4', '42'])).
% 0.20/0.55  thf('61', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i]:
% 0.20/0.55         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.20/0.55          | ((X11) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.55  thf('64', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.55  thf('65', plain, (((sk_C) = (k1_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['44', '61', '63', '64'])).
% 0.20/0.55  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.55  thf('67', plain, (((k1_xboole_0) != (sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['43', '65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_xboole_0) != (X0))
% 0.20/0.55          | ~ (v1_xboole_0 @ X0)
% 0.20/0.55          | ~ (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '67'])).
% 0.20/0.55  thf('69', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.55  thf('70', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('72', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (![X0 : $i]: (((k1_xboole_0) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '72'])).
% 0.20/0.55  thf('74', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.55  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.55  thf('76', plain, ($false),
% 0.20/0.55      inference('simplify_reflect+', [status(thm)], ['74', '75'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Az1Oltim7p

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 869 expanded)
%              Number of leaves         :   40 ( 281 expanded)
%              Depth                    :   21
%              Number of atoms          :  835 (7880 expanded)
%              Number of equality atoms :   86 ( 622 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X32 )
      | ~ ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

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

thf('1',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_hidden @ X34 @ ( k1_funct_2 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X34 @ ( k1_funct_2 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) )
        = X15 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( r1_tarski @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('41',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('50',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('51',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['49','51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('55',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('56',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('60',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_C ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('67',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('68',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['62','64','65','66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('70',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['24','68','69','70'])).

thf('72',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('73',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['23','73'])).

thf('75',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['4','75','76'])).

thf('78',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['23','73'])).

thf('81',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('82',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','74'])).

thf('83',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('84',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','74'])).

thf('86',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('87',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['81','82','83','84','85','86'])).

thf('88',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('89',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['80','87','88'])).

thf('90',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Az1Oltim7p
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:10:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 199 iterations in 0.046s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.48  thf(fc3_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.20/0.48       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X32 : $i, X33 : $i]:
% 0.20/0.48         ((v1_xboole_0 @ X32)
% 0.20/0.48          | ~ (v1_xboole_0 @ X33)
% 0.20/0.48          | (v1_xboole_0 @ (k1_funct_2 @ X32 @ X33)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.20/0.48  thf(t169_funct_2, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.20/0.48         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.48           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.20/0.48            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.48              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.20/0.48  thf('1', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d1_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.48  thf('3', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.48  thf(d1_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_1, axiom,
% 0.20/0.48    (![B:$i,A:$i]:
% 0.20/0.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.48       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X24 : $i, X25 : $i]:
% 0.20/0.48         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.48  thf('6', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t121_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.20/0.48       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.20/0.48          | ~ (r2_hidden @ X34 @ (k1_funct_2 @ X35 @ X36)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_3, axiom,
% 0.20/0.48    (![C:$i,B:$i,A:$i]:
% 0.20/0.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.48  thf(zf_stmt_5, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.48         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.20/0.48          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.20/0.48          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.20/0.48        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '10'])).
% 0.20/0.48  thf('12', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.48         ((v1_funct_2 @ X34 @ X35 @ X36)
% 0.20/0.48          | ~ (r2_hidden @ X34 @ (k1_funct_2 @ X35 @ X36)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.20/0.48  thf('14', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.48         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.20/0.48          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.20/0.48          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.20/0.48        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.48         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.20/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.20/0.48        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.20/0.48        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.20/0.48         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf(t195_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.48               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (((X14) = (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ (k2_zfmisc_1 @ X14 @ X15)) = (X15))
% 0.20/0.48          | ((X15) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(t3_subset, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('28', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf(t25_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( v1_relat_1 @ B ) =>
% 0.20/0.48           ( ( r1_tarski @ A @ B ) =>
% 0.20/0.48             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.20/0.48               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X16)
% 0.20/0.48          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.20/0.48          | ~ (r1_tarski @ X17 @ X16)
% 0.20/0.48          | ~ (v1_relat_1 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.48        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.48           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.20/0.48        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('33', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X11 : $i, X13 : $i]:
% 0.20/0.48         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.48  thf('35', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf(cc1_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( v1_relat_1 @ C ) ))).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.48         ((v1_relat_1 @ X18)
% 0.20/0.48          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.20/0.48        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '31', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)
% 0.20/0.48        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['25', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf(l13_xboole_0, axiom,
% 0.20/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.48  thf('44', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X4 : $i, X6 : $i]:
% 0.20/0.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X1 @ X0)
% 0.20/0.48          | ~ (v1_xboole_0 @ X0)
% 0.20/0.48          | ((X1) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((((sk_C) = (k1_xboole_0))
% 0.20/0.48        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))
% 0.20/0.48         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '48'])).
% 0.20/0.48  thf(t113_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.48  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (((((sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '51', '52'])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('55', plain,
% 0.20/0.48      (((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ sk_B_1)
% 0.20/0.48         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.48  thf(t60_relat_1, axiom,
% 0.20/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('56', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.48  thf('57', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.48  thf('59', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (![X4 : $i, X6 : $i]:
% 0.20/0.48         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C)
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ sk_C)
% 0.20/0.48         | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C))))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['58', '61'])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i]:
% 0.20/0.48         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.48  thf('64', plain,
% 0.20/0.48      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.48  thf('65', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      ((((k1_xboole_0) = (sk_C)))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.20/0.48      inference('demod', [status(thm)], ['62', '64', '65', '66', '67'])).
% 0.20/0.48  thf('69', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.48  thf('70', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf('71', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.20/0.48      inference('demod', [status(thm)], ['24', '68', '69', '70'])).
% 0.20/0.48  thf('72', plain,
% 0.20/0.48      (~ (((k1_relat_1 @ sk_C) = (sk_A))) | 
% 0.20/0.48       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('73', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.20/0.48  thf('74', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['23', '73'])).
% 0.20/0.48  thf('75', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['21', '74'])).
% 0.20/0.48  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.48  thf('77', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '75', '76'])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.48  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.48  thf('80', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['23', '73'])).
% 0.20/0.48  thf('81', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C)
% 0.20/0.48        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.48  thf('82', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['21', '74'])).
% 0.20/0.48  thf('83', plain,
% 0.20/0.48      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.48  thf('84', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf('85', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['21', '74'])).
% 0.20/0.48  thf('86', plain,
% 0.20/0.48      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.48  thf('87', plain, (((k1_xboole_0) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['81', '82', '83', '84', '85', '86'])).
% 0.20/0.48  thf('88', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.48  thf('89', plain, (((k1_xboole_0) != (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['80', '87', '88'])).
% 0.20/0.48  thf('90', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['79', '89'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

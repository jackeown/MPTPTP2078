%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hm70cN7csg

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:25 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 814 expanded)
%              Number of leaves         :   40 ( 265 expanded)
%              Depth                    :   22
%              Number of atoms          :  806 (7499 expanded)
%              Number of equality atoms :   86 ( 607 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) )
        = X17 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('4',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_hidden @ X33 @ ( k1_funct_2 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ ( k2_relat_1 @ X18 ) )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','13'])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['24','26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('31',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = sk_C ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('43',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','39','40','41','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('45',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['2','43','44','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

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

thf('51',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('53',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('54',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( r2_hidden @ X33 @ ( k1_funct_2 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('67',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('69',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('71',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('72',plain,(
    k1_xboole_0 = sk_C ),
    inference(demod,[status(thm)],['50','67','68','69','70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('74',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['49','72','73'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('75',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('76',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['74','84'])).

thf('86',plain,(
    $false ),
    inference(simplify,[status(thm)],['85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hm70cN7csg
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:09:04 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.36/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.61  % Solved by: fo/fo7.sh
% 0.36/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.61  % done 209 iterations in 0.128s
% 0.36/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.61  % SZS output start Refutation
% 0.36/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.61  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.36/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.61  thf(t169_funct_2, conjecture,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.61       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.36/0.61         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.36/0.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.61        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.61          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.36/0.61            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.36/0.61              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.36/0.61    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.36/0.61  thf('0', plain,
% 0.36/0.61      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.36/0.61        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('1', plain,
% 0.36/0.61      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.36/0.61         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('2', plain,
% 0.36/0.61      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf(t195_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.61          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.36/0.61               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.36/0.61  thf('3', plain,
% 0.36/0.61      (![X16 : $i, X17 : $i]:
% 0.36/0.61         (((X16) = (k1_xboole_0))
% 0.36/0.61          | ((k2_relat_1 @ (k2_zfmisc_1 @ X16 @ X17)) = (X17))
% 0.36/0.61          | ((X17) = (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.36/0.61  thf('4', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(t121_funct_2, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.36/0.61       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.36/0.61  thf('5', plain,
% 0.36/0.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.61         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.36/0.61          | ~ (r2_hidden @ X33 @ (k1_funct_2 @ X34 @ X35)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.36/0.61  thf('6', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf(t3_subset, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.61  thf('7', plain,
% 0.36/0.61      (![X11 : $i, X12 : $i]:
% 0.36/0.61         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.61  thf('8', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf(t25_relat_1, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( v1_relat_1 @ A ) =>
% 0.36/0.61       ( ![B:$i]:
% 0.36/0.61         ( ( v1_relat_1 @ B ) =>
% 0.36/0.61           ( ( r1_tarski @ A @ B ) =>
% 0.36/0.61             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.36/0.61               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.36/0.61  thf('9', plain,
% 0.36/0.61      (![X18 : $i, X19 : $i]:
% 0.36/0.61         (~ (v1_relat_1 @ X18)
% 0.36/0.61          | (r1_tarski @ (k2_relat_1 @ X19) @ (k2_relat_1 @ X18))
% 0.36/0.61          | ~ (r1_tarski @ X19 @ X18)
% 0.36/0.61          | ~ (v1_relat_1 @ X19))),
% 0.36/0.61      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.36/0.61  thf('10', plain,
% 0.36/0.61      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.61        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.36/0.61           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.36/0.61        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.61  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(fc6_relat_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.61  thf('12', plain,
% 0.36/0.61      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.36/0.61      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.61  thf('13', plain,
% 0.36/0.61      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.36/0.61        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.36/0.61  thf('14', plain,
% 0.36/0.61      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)
% 0.36/0.61        | ((sk_B_1) = (k1_xboole_0))
% 0.36/0.61        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.61      inference('sup+', [status(thm)], ['3', '13'])).
% 0.36/0.61  thf('15', plain,
% 0.36/0.61      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('16', plain,
% 0.36/0.61      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.61  thf('17', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf(l13_xboole_0, axiom,
% 0.36/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.61  thf('18', plain,
% 0.36/0.61      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.61  thf('19', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.61  thf(d10_xboole_0, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.61  thf('20', plain,
% 0.36/0.61      (![X4 : $i, X6 : $i]:
% 0.36/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.36/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.61  thf('21', plain,
% 0.36/0.61      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.61  thf('22', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]:
% 0.36/0.61         (~ (r1_tarski @ X1 @ X0)
% 0.36/0.61          | ~ (v1_xboole_0 @ X0)
% 0.36/0.61          | ((X1) = (k1_xboole_0)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.36/0.61  thf('23', plain,
% 0.36/0.61      ((((sk_C) = (k1_xboole_0))
% 0.36/0.61        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['17', '22'])).
% 0.36/0.61  thf('24', plain,
% 0.36/0.61      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 0.36/0.61         | ((sk_A) = (k1_xboole_0))
% 0.36/0.61         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['16', '23'])).
% 0.36/0.61  thf(t113_zfmisc_1, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.61  thf('25', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i]:
% 0.36/0.61         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.61  thf('26', plain,
% 0.36/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['25'])).
% 0.36/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.61  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.61  thf('28', plain,
% 0.36/0.61      (((((sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('demod', [status(thm)], ['24', '26', '27'])).
% 0.36/0.61  thf('29', plain,
% 0.36/0.61      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('30', plain,
% 0.36/0.61      (((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ sk_B_1)
% 0.36/0.61         | ((sk_A) = (k1_xboole_0))))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.61  thf(t60_relat_1, axiom,
% 0.36/0.61    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.36/0.61     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.36/0.61  thf('31', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.61  thf('32', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.61  thf('33', plain,
% 0.36/0.61      ((((sk_A) = (k1_xboole_0)))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.36/0.61  thf('34', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.61  thf('35', plain,
% 0.36/0.61      (![X4 : $i, X6 : $i]:
% 0.36/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.36/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.61  thf('36', plain,
% 0.36/0.61      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C)
% 0.36/0.61        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.61  thf('37', plain,
% 0.36/0.61      (((~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1) @ sk_C)
% 0.36/0.61         | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C))))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['33', '36'])).
% 0.36/0.61  thf('38', plain,
% 0.36/0.61      (![X9 : $i, X10 : $i]:
% 0.36/0.61         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.61  thf('39', plain,
% 0.36/0.61      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.61  thf('40', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.61  thf('41', plain,
% 0.36/0.61      ((((sk_A) = (k1_xboole_0)))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.36/0.61  thf('42', plain,
% 0.36/0.61      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['38'])).
% 0.36/0.61  thf('43', plain,
% 0.36/0.61      ((((k1_xboole_0) = (sk_C)))
% 0.36/0.61         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.36/0.61      inference('demod', [status(thm)], ['37', '39', '40', '41', '42'])).
% 0.36/0.61  thf('44', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.61  thf('45', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.61  thf('46', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.36/0.61      inference('demod', [status(thm)], ['2', '43', '44', '45'])).
% 0.36/0.61  thf('47', plain,
% 0.36/0.61      (~ (((k1_relat_1 @ sk_C) = (sk_A))) | 
% 0.36/0.61       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.36/0.61      inference('split', [status(esa)], ['0'])).
% 0.36/0.61  thf('48', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.36/0.61      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.36/0.61  thf('49', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.36/0.61      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.36/0.61  thf('50', plain,
% 0.36/0.61      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C)
% 0.36/0.61        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.61  thf(d1_funct_2, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_1, axiom,
% 0.36/0.61    (![B:$i,A:$i]:
% 0.36/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.61  thf('51', plain,
% 0.36/0.61      (![X23 : $i, X24 : $i]:
% 0.36/0.61         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.61  thf('52', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.61  thf(zf_stmt_3, axiom,
% 0.36/0.61    (![C:$i,B:$i,A:$i]:
% 0.36/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.61  thf(zf_stmt_5, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.61  thf('53', plain,
% 0.36/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.36/0.61         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.36/0.61          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.36/0.61          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.61  thf('54', plain,
% 0.36/0.61      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.36/0.61        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.61  thf('55', plain,
% 0.36/0.61      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['51', '54'])).
% 0.36/0.61  thf('56', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf('57', plain,
% 0.36/0.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.36/0.61         ((v1_funct_2 @ X33 @ X34 @ X35)
% 0.36/0.61          | ~ (r2_hidden @ X33 @ (k1_funct_2 @ X34 @ X35)))),
% 0.36/0.61      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.36/0.61  thf('58', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.36/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.61  thf('59', plain,
% 0.36/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.36/0.61         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.36/0.61          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.36/0.61          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.61  thf('60', plain,
% 0.36/0.61      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.36/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.36/0.61  thf('61', plain,
% 0.36/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.61    (![A:$i,B:$i,C:$i]:
% 0.36/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.61  thf('62', plain,
% 0.36/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.61         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.36/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.36/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.61  thf('63', plain,
% 0.36/0.61      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.36/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.61  thf('64', plain,
% 0.36/0.61      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.36/0.61        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.36/0.61      inference('demod', [status(thm)], ['60', '63'])).
% 0.36/0.61  thf('65', plain,
% 0.36/0.61      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.36/0.61      inference('sup-', [status(thm)], ['55', '64'])).
% 0.36/0.61  thf('66', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.36/0.61      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.36/0.61  thf('67', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.36/0.61  thf('68', plain,
% 0.36/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['25'])).
% 0.36/0.61  thf('69', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.36/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.61  thf('70', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.36/0.61  thf('71', plain,
% 0.36/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify', [status(thm)], ['25'])).
% 0.36/0.61  thf('72', plain, (((k1_xboole_0) = (sk_C))),
% 0.36/0.61      inference('demod', [status(thm)], ['50', '67', '68', '69', '70', '71'])).
% 0.36/0.61  thf('73', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.61      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.36/0.61  thf('74', plain, (((k1_xboole_0) != (sk_A))),
% 0.36/0.61      inference('demod', [status(thm)], ['49', '72', '73'])).
% 0.36/0.61  thf(fc3_funct_2, axiom,
% 0.36/0.61    (![A:$i,B:$i]:
% 0.36/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.36/0.61       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.36/0.61  thf('75', plain,
% 0.36/0.61      (![X31 : $i, X32 : $i]:
% 0.36/0.61         ((v1_xboole_0 @ X31)
% 0.36/0.61          | ~ (v1_xboole_0 @ X32)
% 0.36/0.61          | (v1_xboole_0 @ (k1_funct_2 @ X31 @ X32)))),
% 0.36/0.61      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.36/0.61  thf('76', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.36/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.61  thf(d1_xboole_0, axiom,
% 0.36/0.61    (![A:$i]:
% 0.36/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.36/0.61  thf('77', plain,
% 0.36/0.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.36/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.36/0.61  thf('78', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.36/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.36/0.61  thf('79', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.36/0.61      inference('sup-', [status(thm)], ['75', '78'])).
% 0.36/0.61  thf('80', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.36/0.61      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.36/0.61  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.61  thf('82', plain, ((v1_xboole_0 @ sk_A)),
% 0.36/0.61      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.36/0.61  thf('83', plain,
% 0.36/0.61      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.36/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.61  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.61      inference('sup-', [status(thm)], ['82', '83'])).
% 0.36/0.61  thf('85', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.61      inference('demod', [status(thm)], ['74', '84'])).
% 0.36/0.61  thf('86', plain, ($false), inference('simplify', [status(thm)], ['85'])).
% 0.36/0.61  
% 0.36/0.61  % SZS output end Refutation
% 0.36/0.61  
% 0.36/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

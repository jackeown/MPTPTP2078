%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HmYpO1eZaK

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 425 expanded)
%              Number of leaves         :   40 ( 145 expanded)
%              Depth                    :   21
%              Number of atoms          :  743 (3768 expanded)
%              Number of equality atoms :   79 ( 307 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X29 @ X30 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_hidden @ X31 @ ( k1_funct_2 @ X32 @ X33 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( r2_hidden @ X31 @ ( k1_funct_2 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('36',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('44',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','44','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('48',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('49',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('50',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('53',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('55',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('57',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['24','57','58','59'])).

thf('61',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('62',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['23','62'])).

thf('64',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['4','64','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['23','62'])).

thf('70',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('71',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','63'])).

thf('72',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('76',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['69','74','75'])).

thf('77',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HmYpO1eZaK
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:09:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 210 iterations in 0.121s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.21/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(fc3_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.57       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X29 : $i, X30 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ X29)
% 0.21/0.57          | ~ (v1_xboole_0 @ X30)
% 0.21/0.57          | (v1_xboole_0 @ (k1_funct_2 @ X29 @ X30)))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.21/0.57  thf(t169_funct_2, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.57         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.57           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.57            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.57              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.21/0.57  thf('1', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d1_xboole_0, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf('3', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.57  thf('4', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.57  thf(d1_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_1, axiom,
% 0.21/0.57    (![B:$i,A:$i]:
% 0.21/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X21 : $i, X22 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.57  thf('6', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t121_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.57       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.21/0.57          | ~ (r2_hidden @ X31 @ (k1_funct_2 @ X32 @ X33)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_3, axiom,
% 0.21/0.57    (![C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_5, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.57         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.21/0.57          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.21/0.57          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.57        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.57  thf('12', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         ((v1_funct_2 @ X31 @ X32 @ X33)
% 0.21/0.57          | ~ (r2_hidden @ X31 @ (k1_funct_2 @ X32 @ X33)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.21/0.57  thf('14', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.57         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.21/0.57          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.21/0.57          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.57         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.21/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.57        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.21/0.57      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '20'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.21/0.57        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.21/0.57         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['22'])).
% 0.21/0.57  thf(t195_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.57               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X14 : $i, X15 : $i]:
% 0.21/0.57         (((X14) = (k1_xboole_0))
% 0.21/0.57          | ((k2_relat_1 @ (k2_zfmisc_1 @ X14 @ X15)) = (X15))
% 0.21/0.57          | ((X15) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf(t3_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i]:
% 0.21/0.57         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('28', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf(t25_relat_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( v1_relat_1 @ B ) =>
% 0.21/0.57           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.57             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.57               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X16)
% 0.21/0.57          | (r1_tarski @ (k2_relat_1 @ X17) @ (k2_relat_1 @ X16))
% 0.21/0.57          | ~ (r1_tarski @ X17 @ X16)
% 0.21/0.57          | ~ (v1_relat_1 @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.57        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.57           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.21/0.57        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(fc6_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.57        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)
% 0.21/0.57        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.57        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup+', [status(thm)], ['25', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['22'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.57  thf('37', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf(l13_xboole_0, axiom,
% 0.21/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.57  thf(t3_xboole_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.57          | ~ (v1_xboole_0 @ X0)
% 0.21/0.57          | ((X1) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0))
% 0.21/0.57        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 0.21/0.57         | ((sk_A) = (k1_xboole_0))
% 0.21/0.57         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.57  thf(t113_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.57       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.57  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((((sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['42', '44', '45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['22'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ sk_B_1)
% 0.21/0.57         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf(t60_relat_1, axiom,
% 0.21/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.57  thf('49', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.57  thf('50', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0))
% 0.21/0.57        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.21/0.57         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i]:
% 0.21/0.57         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['54'])).
% 0.21/0.57  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['53', '55', '56'])).
% 0.21/0.57  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.57  thf('59', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf('60', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['24', '57', '58', '59'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (~ (((k1_relat_1 @ sk_C) = (sk_A))) | 
% 0.21/0.57       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.57      inference('split', [status(esa)], ['22'])).
% 0.21/0.57  thf('62', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.21/0.57  thf('63', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['23', '62'])).
% 0.21/0.57  thf('64', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['21', '63'])).
% 0.21/0.57  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.57  thf('66', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['4', '64', '65'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.57  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.57  thf('69', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['23', '62'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0))
% 0.21/0.57        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '40'])).
% 0.21/0.57  thf('71', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['21', '63'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (![X7 : $i]: ((k2_zfmisc_1 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.57  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.57  thf('74', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.57      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.21/0.57  thf('75', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.57  thf('76', plain, (((k1_xboole_0) != (sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['69', '74', '75'])).
% 0.21/0.57  thf('77', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['68', '76'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KH4BT0lle9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 412 expanded)
%              Number of leaves         :   43 ( 142 expanded)
%              Depth                    :   21
%              Number of atoms          :  760 (3731 expanded)
%              Number of equality atoms :   83 ( 303 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X34 @ X35 ) ) ) ),
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
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ),
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
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A_1 ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_hidden @ X36 @ ( k1_funct_2 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( r2_hidden @ X36 @ ( k1_funct_2 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('14',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('19',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A_1 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A_1 )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A_1 ) ),
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
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) )
        = X19 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X21 ) @ ( k2_relat_1 @ X20 ) )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('36',plain,
    ( ( ( sk_A_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A_1 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X11 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_A_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','42','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('46',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ sk_B_1 )
      | ( sk_A_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('48',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('49',plain,
    ( ( sk_A_1 = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_zfmisc_1 @ X10 @ X11 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('53',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X11 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','53','54'])).

thf('56',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('57',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('58',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['24','55','56','57'])).

thf('59',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A_1 )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('60',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A_1 ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A_1 ),
    inference(simpl_trail,[status(thm)],['23','60'])).

thf('62',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','61'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('63',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('64',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('65',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('66',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    v1_xboole_0 @ sk_A_1 ),
    inference(demod,[status(thm)],['4','62','67'])).

thf('69',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,(
    sk_A_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A_1 ),
    inference(simpl_trail,[status(thm)],['23','60'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('73',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','61'])).

thf('74',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('75',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('76',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('78',plain,(
    k1_xboole_0 != sk_A_1 ),
    inference(demod,[status(thm)],['71','76','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KH4BT0lle9
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 139 iterations in 0.068s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.21/0.52  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.21/0.52  thf(fc3_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.52       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X34 : $i, X35 : $i]:
% 0.21/0.52         ((v1_xboole_0 @ X34)
% 0.21/0.52          | ~ (v1_xboole_0 @ X35)
% 0.21/0.52          | (v1_xboole_0 @ (k1_funct_2 @ X34 @ X35)))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.21/0.52  thf(t169_funct_2, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.52         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.52           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.52          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.52            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.52              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.21/0.52  thf('1', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d1_xboole_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.52  thf('3', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf('4', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.52  thf(d1_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.52           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.52             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.52         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.52           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.52             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, axiom,
% 0.21/0.52    (![B:$i,A:$i]:
% 0.21/0.52     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.52       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X26 : $i, X27 : $i]:
% 0.21/0.52         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.52  thf('6', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t121_funct_2, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.52       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.52         ((m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.21/0.52          | ~ (r2_hidden @ X36 @ (k1_funct_2 @ X37 @ X38)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_3, axiom,
% 0.21/0.52    (![C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.52       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_5, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.52           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.52         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.21/0.52          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.21/0.52          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 0.21/0.52        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.52  thf('12', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A_1 @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.21/0.52         ((v1_funct_2 @ X36 @ X37 @ X38)
% 0.21/0.52          | ~ (r2_hidden @ X36 @ (k1_funct_2 @ X37 @ X38)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.21/0.52  thf('14', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.52         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.21/0.52          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.21/0.52          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 0.21/0.52        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.52         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 0.21/0.52        | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A_1) = (k1_relat_1 @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((((k1_relat_1 @ sk_C) != (sk_A_1))
% 0.21/0.52        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((((k1_relat_1 @ sk_C) != (sk_A_1)))
% 0.21/0.52         <= (~ (((k1_relat_1 @ sk_C) = (sk_A_1))))),
% 0.21/0.52      inference('split', [status(esa)], ['22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['22'])).
% 0.21/0.52  thf(t195_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.52               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (((X18) = (k1_xboole_0))
% 0.21/0.52          | ((k2_relat_1 @ (k2_zfmisc_1 @ X18 @ X19)) = (X19))
% 0.21/0.52          | ((X19) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('28', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf(t25_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.52             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.52               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X20)
% 0.21/0.52          | (r1_tarski @ (k2_relat_1 @ X21) @ (k2_relat_1 @ X20))
% 0.21/0.52          | ~ (r1_tarski @ X21 @ X20)
% 0.21/0.52          | ~ (v1_relat_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.52        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.52           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))
% 0.21/0.52        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(fc6_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.52        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A_1) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['25', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['22'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((((sk_A_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf(l32_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X4 : $i, X6 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (((((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A_1 @ k1_xboole_0))
% 0.21/0.52           = (k1_xboole_0))
% 0.21/0.52         | ((sk_A_1) = (k1_xboole_0))))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['36', '39'])).
% 0.21/0.52  thf(t113_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.21/0.52          | ((X11) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.52  thf(t3_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('43', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((((sk_C) = (k1_xboole_0)) | ((sk_A_1) = (k1_xboole_0))))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['22'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ sk_B_1)
% 0.21/0.52         | ((sk_A_1) = (k1_xboole_0))))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.52  thf(t60_relat_1, axiom,
% 0.21/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('47', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.52  thf('48', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((((sk_A_1) = (k1_xboole_0)))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.21/0.52          = (k1_xboole_0)))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X10 @ X11) = (k1_xboole_0))
% 0.21/0.52          | ((X10) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X11 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X11) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.52  thf('54', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.52         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['51', '53', '54'])).
% 0.21/0.52  thf('56', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.52  thf('57', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.52  thf('58', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '55', '56', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (~ (((k1_relat_1 @ sk_C) = (sk_A_1))) | 
% 0.21/0.52       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.52      inference('split', [status(esa)], ['22'])).
% 0.21/0.52  thf('60', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A_1)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('61', plain, (((k1_relat_1 @ sk_C) != (sk_A_1))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['23', '60'])).
% 0.21/0.52  thf('62', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['21', '61'])).
% 0.21/0.52  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.21/0.52  thf('63', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.52  thf('64', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.21/0.52  thf(l13_xboole_0, axiom,
% 0.21/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.52  thf('66', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.52  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('demod', [status(thm)], ['63', '66'])).
% 0.21/0.52  thf('68', plain, ((v1_xboole_0 @ sk_A_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '62', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.52  thf('70', plain, (((sk_A_1) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.52  thf('71', plain, (((k1_relat_1 @ sk_C) != (sk_A_1))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['23', '60'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (((k4_xboole_0 @ sk_C @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.52  thf('73', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['21', '61'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      (![X10 : $i]: ((k2_zfmisc_1 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.52  thf('75', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('76', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 0.21/0.52  thf('77', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.52  thf('78', plain, (((k1_xboole_0) != (sk_A_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['71', '76', '77'])).
% 0.21/0.52  thf('79', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['70', '78'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

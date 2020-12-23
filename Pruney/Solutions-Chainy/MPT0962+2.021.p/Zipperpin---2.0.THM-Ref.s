%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zm9NeOprbY

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:51 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 369 expanded)
%              Number of leaves         :   35 ( 117 expanded)
%              Depth                    :   16
%              Number of atoms          :  630 (3820 expanded)
%              Number of equality atoms :   36 ( 104 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( r1_xboole_0 @ X10 @ X10 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('2',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['1'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('17',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X29 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('24',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['32'])).

thf('36',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['32'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['32'])).

thf('41',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['36','39','40'])).

thf('42',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['33','41'])).

thf('43',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['31','42'])).

thf('44',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['25','43'])).

thf('45',plain,
    ( ~ ( zip_tseitin_0 @ sk_A @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','44'])).

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('47',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','47'])).

thf('49',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('51',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('53',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['25','43'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','6'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','54','55','56'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('58',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','6'])).

thf('61',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('64',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['4','6'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['48','64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zm9NeOprbY
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:29:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 228 iterations in 0.330s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.79  thf(fc10_relat_1, axiom,
% 0.59/0.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (![X22 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (k1_relat_1 @ X22)) | ~ (v1_xboole_0 @ X22))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.59/0.79  thf(t66_xboole_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.59/0.79       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X10 : $i]: ((r1_xboole_0 @ X10 @ X10) | ((X10) != (k1_xboole_0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.59/0.79  thf('2', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('simplify', [status(thm)], ['1'])).
% 0.59/0.79  thf(t69_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.59/0.79       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X12 : $i, X13 : $i]:
% 0.59/0.79         (~ (r1_xboole_0 @ X12 @ X13)
% 0.59/0.79          | ~ (r1_tarski @ X12 @ X13)
% 0.59/0.79          | (v1_xboole_0 @ X12))),
% 0.59/0.79      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf(d10_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('6', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.59/0.79      inference('simplify', [status(thm)], ['5'])).
% 0.59/0.79  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '6'])).
% 0.59/0.79  thf(d3_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X4 : $i, X6 : $i]:
% 0.59/0.79         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf(d1_xboole_0, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X7 : $i, X9 : $i]:
% 0.59/0.79         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['10', '13'])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['7', '14'])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k1_relat_1 @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '15'])).
% 0.59/0.79  thf(t4_funct_2, conjecture,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.79       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.59/0.79         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.59/0.79           ( m1_subset_1 @
% 0.59/0.79             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i,B:$i]:
% 0.59/0.79        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.79          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.59/0.79            ( ( v1_funct_1 @ B ) & 
% 0.59/0.79              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.59/0.79              ( m1_subset_1 @
% 0.59/0.79                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.59/0.79  thf('17', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('18', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.59/0.79      inference('simplify', [status(thm)], ['5'])).
% 0.59/0.79  thf(t11_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ C ) =>
% 0.59/0.79       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.59/0.79           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.59/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.79         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 0.59/0.79          | ~ (r1_tarski @ (k2_relat_1 @ X27) @ X29)
% 0.59/0.79          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.59/0.79          | ~ (v1_relat_1 @ X27))),
% 0.59/0.79      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | (m1_subset_1 @ X0 @ 
% 0.59/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.59/0.79          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['18', '19'])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (((m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['17', '20'])).
% 0.59/0.79  thf('22', plain, ((v1_relat_1 @ sk_B_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf(d1_funct_2, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.59/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.59/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.59/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.59/0.79  thf(zf_stmt_2, axiom,
% 0.59/0.79    (![C:$i,B:$i,A:$i]:
% 0.59/0.79     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.59/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.79  thf(zf_stmt_4, axiom,
% 0.59/0.79    (![B:$i,A:$i]:
% 0.59/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.79       ( zip_tseitin_0 @ B @ A ) ))).
% 0.59/0.79  thf(zf_stmt_5, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.59/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.59/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.59/0.79         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.59/0.79          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.59/0.79          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.59/0.79        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.79         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.59/0.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.59/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.59/0.79         = (k1_relat_1 @ sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.79         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 0.59/0.79          | (v1_funct_2 @ X34 @ X32 @ X33)
% 0.59/0.79          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.59/0.79        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.59/0.79        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['28', '29'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.59/0.79        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['30'])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ sk_B_1)
% 0.59/0.79        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.59/0.79        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.59/0.79         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.59/0.79      inference('split', [status(esa)], ['32'])).
% 0.59/0.79  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('35', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.59/0.79      inference('split', [status(esa)], ['32'])).
% 0.59/0.79  thf('36', plain, (((v1_funct_1 @ sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['21', '22'])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.59/0.79      inference('split', [status(esa)], ['32'])).
% 0.59/0.79  thf('39', plain,
% 0.59/0.79      (((m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.59/0.79       ~
% 0.59/0.79       ((m1_subset_1 @ sk_B_1 @ 
% 0.59/0.79         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.59/0.79       ~ ((v1_funct_1 @ sk_B_1))),
% 0.59/0.79      inference('split', [status(esa)], ['32'])).
% 0.59/0.79  thf('41', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.59/0.79      inference('sat_resolution*', [status(thm)], ['36', '39', '40'])).
% 0.59/0.79  thf('42', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.59/0.79      inference('simpl_trail', [status(thm)], ['33', '41'])).
% 0.59/0.79  thf('43', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.59/0.79      inference('clc', [status(thm)], ['31', '42'])).
% 0.59/0.79  thf('44', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.59/0.79      inference('clc', [status(thm)], ['25', '43'])).
% 0.59/0.79  thf('45', plain,
% 0.59/0.79      ((~ (zip_tseitin_0 @ sk_A @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['16', '44'])).
% 0.59/0.79  thf('46', plain,
% 0.59/0.79      (![X30 : $i, X31 : $i]:
% 0.59/0.79         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.79  thf('47', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 0.59/0.79      inference('simplify', [status(thm)], ['46'])).
% 0.59/0.79  thf('48', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.79      inference('demod', [status(thm)], ['45', '47'])).
% 0.59/0.79  thf('49', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('50', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      ((((k2_relat_1 @ sk_B_1) = (sk_A)) | ~ (v1_xboole_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['49', '50'])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (![X30 : $i, X31 : $i]:
% 0.59/0.79         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.79  thf('53', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.59/0.79      inference('clc', [status(thm)], ['25', '43'])).
% 0.59/0.79  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '6'])).
% 0.59/0.79  thf('57', plain, (((k2_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['51', '54', '55', '56'])).
% 0.59/0.79  thf(fc9_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.59/0.79       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.59/0.79  thf('58', plain,
% 0.59/0.79      (![X23 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ (k2_relat_1 @ X23))
% 0.59/0.79          | ~ (v1_relat_1 @ X23)
% 0.59/0.79          | (v1_xboole_0 @ X23))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.59/0.79  thf('59', plain,
% 0.59/0.79      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.79        | ~ (v1_relat_1 @ sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['57', '58'])).
% 0.59/0.79  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '6'])).
% 0.59/0.79  thf('61', plain, ((v1_relat_1 @ sk_B_1)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('62', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.59/0.79      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.59/0.79  thf('63', plain,
% 0.59/0.79      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['7', '14'])).
% 0.59/0.79  thf('64', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['62', '63'])).
% 0.59/0.79  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '6'])).
% 0.59/0.79  thf('66', plain, ($false),
% 0.59/0.79      inference('demod', [status(thm)], ['48', '64', '65'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

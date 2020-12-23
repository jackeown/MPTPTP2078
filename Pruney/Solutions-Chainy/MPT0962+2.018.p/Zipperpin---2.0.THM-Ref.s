%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Uy0A020fgE

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:51 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 261 expanded)
%              Number of leaves         :   46 (  94 expanded)
%              Depth                    :   23
%              Number of atoms          :  996 (2470 expanded)
%              Number of equality atoms :   46 (  65 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X36 ) @ X37 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X36 ) @ X38 )
      | ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('25',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('28',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_B_1 ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ sk_A @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_B_1 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','39'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) )
      | ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('52',plain,(
    ! [X31: $i] :
      ( ( ( k3_relat_1 @ X31 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('54',plain,(
    ! [X31: $i] :
      ( ( ( k3_relat_1 @ X31 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X31 ) @ ( k1_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ sk_B_1 )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) ) )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X19: $i] :
      ( ( k2_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ sk_B_1 )
        = ( k1_relat_1 @ sk_B_1 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['55','58','59'])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('61',plain,(
    ! [X32: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X32 ) )
      | ~ ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X47: $i] :
      ( ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ) )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_zfmisc_1 @ X26 @ X27 )
        = k1_xboole_0 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('67',plain,(
    ! [X26: $i] :
      ( ( k2_zfmisc_1 @ X26 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['65','67','68','69'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('71',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( r1_tarski @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['62','76'])).

thf('78',plain,(
    ! [X31: $i] :
      ( ( ( k3_relat_1 @ X31 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X31 ) @ ( k1_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('80',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['77','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('91',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('92',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['90','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( zip_tseitin_0 @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['89','93'])).

thf('95',plain,(
    zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(eq_fact,[status(thm)],['94'])).

thf('96',plain,(
    zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['23','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['17','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Uy0A020fgE
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:35:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.21  % Solved by: fo/fo7.sh
% 0.99/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.21  % done 1312 iterations in 0.756s
% 0.99/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.21  % SZS output start Refutation
% 0.99/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.99/1.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.99/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.99/1.21  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.99/1.21  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.99/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.99/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.21  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.21  thf(sk_B_type, type, sk_B: $i > $i).
% 0.99/1.21  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.99/1.21  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.99/1.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.99/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.99/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.99/1.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.99/1.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.99/1.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.99/1.21  thf(t4_funct_2, conjecture,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.21       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.99/1.21         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.99/1.21           ( m1_subset_1 @
% 0.99/1.21             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.99/1.21  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.21    (~( ![A:$i,B:$i]:
% 0.99/1.21        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.99/1.21          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.99/1.21            ( ( v1_funct_1 @ B ) & 
% 0.99/1.21              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.99/1.21              ( m1_subset_1 @
% 0.99/1.21                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.99/1.21    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.99/1.21  thf('0', plain,
% 0.99/1.21      ((~ (v1_funct_1 @ sk_B_1)
% 0.99/1.21        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.99/1.21        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('1', plain,
% 0.99/1.21      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.99/1.21         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.99/1.21      inference('split', [status(esa)], ['0'])).
% 0.99/1.21  thf('2', plain, ((v1_funct_1 @ sk_B_1)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('3', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.99/1.21      inference('split', [status(esa)], ['0'])).
% 0.99/1.21  thf('4', plain, (((v1_funct_1 @ sk_B_1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 0.99/1.21  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(d10_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.21  thf('6', plain,
% 0.99/1.21      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 0.99/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.21  thf('7', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 0.99/1.21      inference('simplify', [status(thm)], ['6'])).
% 0.99/1.21  thf(t11_relset_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( v1_relat_1 @ C ) =>
% 0.99/1.21       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.99/1.21           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.99/1.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.99/1.21  thf('8', plain,
% 0.99/1.21      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.99/1.21         (~ (r1_tarski @ (k1_relat_1 @ X36) @ X37)
% 0.99/1.21          | ~ (r1_tarski @ (k2_relat_1 @ X36) @ X38)
% 0.99/1.21          | (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.99/1.21          | ~ (v1_relat_1 @ X36))),
% 0.99/1.21      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.99/1.21  thf('9', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         (~ (v1_relat_1 @ X0)
% 0.99/1.21          | (m1_subset_1 @ X0 @ 
% 0.99/1.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.99/1.21          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 0.99/1.21  thf('10', plain,
% 0.99/1.21      (((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.99/1.21        | ~ (v1_relat_1 @ sk_B_1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['5', '9'])).
% 0.99/1.21  thf('11', plain, ((v1_relat_1 @ sk_B_1)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('12', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['10', '11'])).
% 0.99/1.21  thf('13', plain,
% 0.99/1.21      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.99/1.21         <= (~
% 0.99/1.21             ((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.99/1.21      inference('split', [status(esa)], ['0'])).
% 0.99/1.21  thf('14', plain,
% 0.99/1.21      (((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.99/1.21      inference('sup-', [status(thm)], ['12', '13'])).
% 0.99/1.21  thf('15', plain,
% 0.99/1.21      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.99/1.21       ~
% 0.99/1.21       ((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.99/1.21       ~ ((v1_funct_1 @ sk_B_1))),
% 0.99/1.21      inference('split', [status(esa)], ['0'])).
% 0.99/1.21  thf('16', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.99/1.21      inference('sat_resolution*', [status(thm)], ['4', '14', '15'])).
% 0.99/1.21  thf('17', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.99/1.21      inference('simpl_trail', [status(thm)], ['1', '16'])).
% 0.99/1.21  thf('18', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['10', '11'])).
% 0.99/1.21  thf(redefinition_k1_relset_1, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.21       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.99/1.21  thf('19', plain,
% 0.99/1.21      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.99/1.21         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.99/1.21          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.99/1.21      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.99/1.21  thf('20', plain,
% 0.99/1.21      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.99/1.21         = (k1_relat_1 @ sk_B_1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.21  thf(d1_funct_2, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.21       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.21           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.99/1.21             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.99/1.21         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.21           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.99/1.21             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.99/1.21  thf(zf_stmt_1, axiom,
% 0.99/1.21    (![C:$i,B:$i,A:$i]:
% 0.99/1.21     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.99/1.21       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.99/1.21  thf('21', plain,
% 0.99/1.21      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.99/1.21         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 0.99/1.21          | (v1_funct_2 @ X43 @ X41 @ X42)
% 0.99/1.21          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.99/1.21  thf('22', plain,
% 0.99/1.21      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.99/1.21        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.99/1.21        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.99/1.21      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.21  thf('23', plain,
% 0.99/1.21      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.99/1.21        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('simplify', [status(thm)], ['22'])).
% 0.99/1.21  thf('24', plain,
% 0.99/1.21      ((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.99/1.21      inference('demod', [status(thm)], ['10', '11'])).
% 0.99/1.21  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.99/1.21  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.99/1.21  thf(zf_stmt_4, axiom,
% 0.99/1.21    (![B:$i,A:$i]:
% 0.99/1.21     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.99/1.21       ( zip_tseitin_0 @ B @ A ) ))).
% 0.99/1.21  thf(zf_stmt_5, axiom,
% 0.99/1.21    (![A:$i,B:$i,C:$i]:
% 0.99/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.99/1.21       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.99/1.21         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.99/1.21           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.99/1.21             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.99/1.21  thf('25', plain,
% 0.99/1.21      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.99/1.21         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.99/1.21          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.99/1.21          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.99/1.21  thf('26', plain,
% 0.99/1.21      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.99/1.21        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['24', '25'])).
% 0.99/1.21  thf('27', plain,
% 0.99/1.21      (![X39 : $i, X40 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.99/1.21  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.99/1.21  thf('28', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.99/1.21      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.99/1.21  thf(t3_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.99/1.21            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.99/1.21       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.99/1.21            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.99/1.21  thf('29', plain,
% 0.99/1.21      (![X10 : $i, X11 : $i]:
% 0.99/1.21         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.99/1.21  thf('30', plain,
% 0.99/1.21      (![X10 : $i, X11 : $i]:
% 0.99/1.21         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.99/1.21  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf(d3_tarski, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( r1_tarski @ A @ B ) <=>
% 0.99/1.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.99/1.21  thf('32', plain,
% 0.99/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.99/1.21         (~ (r2_hidden @ X5 @ X6)
% 0.99/1.21          | (r2_hidden @ X5 @ X7)
% 0.99/1.21          | ~ (r1_tarski @ X6 @ X7))),
% 0.99/1.21      inference('cnf', [status(esa)], [d3_tarski])).
% 0.99/1.21  thf('33', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.21  thf('34', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((r1_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21          | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_B_1) @ X0) @ sk_A))),
% 0.99/1.21      inference('sup-', [status(thm)], ['30', '33'])).
% 0.99/1.21  thf('35', plain,
% 0.99/1.21      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.99/1.21         (~ (r2_hidden @ X12 @ X10)
% 0.99/1.21          | ~ (r2_hidden @ X12 @ X13)
% 0.99/1.21          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.99/1.21  thf('36', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((r1_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21          | ~ (r1_xboole_0 @ sk_A @ X1)
% 0.99/1.21          | ~ (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_B_1) @ X0) @ X1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['34', '35'])).
% 0.99/1.21  thf('37', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((r1_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21          | ~ (r1_xboole_0 @ sk_A @ X0)
% 0.99/1.21          | (r1_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['29', '36'])).
% 0.99/1.21  thf('38', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (~ (r1_xboole_0 @ sk_A @ X0)
% 0.99/1.21          | (r1_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('simplify', [status(thm)], ['37'])).
% 0.99/1.21  thf('39', plain, ((r1_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ sk_B_1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['28', '38'])).
% 0.99/1.21  thf('40', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((r1_xboole_0 @ X0 @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21          | (zip_tseitin_0 @ X0 @ X1))),
% 0.99/1.21      inference('sup+', [status(thm)], ['27', '39'])).
% 0.99/1.21  thf(d1_xboole_0, axiom,
% 0.99/1.21    (![A:$i]:
% 0.99/1.21     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.99/1.21  thf('41', plain,
% 0.99/1.21      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.99/1.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.99/1.21  thf('42', plain,
% 0.99/1.21      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.99/1.21      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.99/1.21  thf('43', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.21  thf('44', plain,
% 0.99/1.21      (((v1_xboole_0 @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ sk_A))),
% 0.99/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.21  thf('45', plain,
% 0.99/1.21      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.99/1.21         (~ (r2_hidden @ X12 @ X10)
% 0.99/1.21          | ~ (r2_hidden @ X12 @ X13)
% 0.99/1.21          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.99/1.21  thf('46', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((v1_xboole_0 @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21          | ~ (r1_xboole_0 @ sk_A @ X0)
% 0.99/1.21          | ~ (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_B_1)) @ X0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['44', '45'])).
% 0.99/1.21  thf('47', plain,
% 0.99/1.21      (((v1_xboole_0 @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21        | ~ (r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21        | (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['41', '46'])).
% 0.99/1.21  thf('48', plain,
% 0.99/1.21      ((~ (r1_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B_1))
% 0.99/1.21        | (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('simplify', [status(thm)], ['47'])).
% 0.99/1.21  thf('49', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ (k2_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['40', '48'])).
% 0.99/1.21  thf(l13_xboole_0, axiom,
% 0.99/1.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.99/1.21  thf('50', plain,
% 0.99/1.21      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 0.99/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.99/1.21  thf('51', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.21  thf(d6_relat_1, axiom,
% 0.99/1.21    (![A:$i]:
% 0.99/1.21     ( ( v1_relat_1 @ A ) =>
% 0.99/1.21       ( ( k3_relat_1 @ A ) =
% 0.99/1.21         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.99/1.21  thf('52', plain,
% 0.99/1.21      (![X31 : $i]:
% 0.99/1.21         (((k3_relat_1 @ X31)
% 0.99/1.21            = (k2_xboole_0 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31)))
% 0.99/1.21          | ~ (v1_relat_1 @ X31))),
% 0.99/1.21      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.99/1.21  thf(commutativity_k2_xboole_0, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.99/1.21  thf('53', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf('54', plain,
% 0.99/1.21      (![X31 : $i]:
% 0.99/1.21         (((k3_relat_1 @ X31)
% 0.99/1.21            = (k2_xboole_0 @ (k2_relat_1 @ X31) @ (k1_relat_1 @ X31)))
% 0.99/1.21          | ~ (v1_relat_1 @ X31))),
% 0.99/1.21      inference('demod', [status(thm)], ['52', '53'])).
% 0.99/1.21  thf('55', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k3_relat_1 @ sk_B_1)
% 0.99/1.21            = (k2_xboole_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B_1)))
% 0.99/1.21          | (zip_tseitin_0 @ sk_A @ X0)
% 0.99/1.21          | ~ (v1_relat_1 @ sk_B_1))),
% 0.99/1.21      inference('sup+', [status(thm)], ['51', '54'])).
% 0.99/1.21  thf('56', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf(t1_boole, axiom,
% 0.99/1.21    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.21  thf('57', plain, (![X19 : $i]: ((k2_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.99/1.21      inference('cnf', [status(esa)], [t1_boole])).
% 0.99/1.21  thf('58', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['56', '57'])).
% 0.99/1.21  thf('59', plain, ((v1_relat_1 @ sk_B_1)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('60', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (((k3_relat_1 @ sk_B_1) = (k1_relat_1 @ sk_B_1))
% 0.99/1.21          | (zip_tseitin_0 @ sk_A @ X0))),
% 0.99/1.21      inference('demod', [status(thm)], ['55', '58', '59'])).
% 0.99/1.21  thf(fc10_relat_1, axiom,
% 0.99/1.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.99/1.21  thf('61', plain,
% 0.99/1.21      (![X32 : $i]:
% 0.99/1.21         ((v1_xboole_0 @ (k1_relat_1 @ X32)) | ~ (v1_xboole_0 @ X32))),
% 0.99/1.21      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.99/1.21  thf('62', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((v1_xboole_0 @ (k3_relat_1 @ sk_B_1))
% 0.99/1.21          | (zip_tseitin_0 @ sk_A @ X0)
% 0.99/1.21          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.99/1.21      inference('sup+', [status(thm)], ['60', '61'])).
% 0.99/1.21  thf('63', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.21  thf(t3_funct_2, axiom,
% 0.99/1.21    (![A:$i]:
% 0.99/1.21     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.99/1.21       ( ( v1_funct_1 @ A ) & 
% 0.99/1.21         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.99/1.21         ( m1_subset_1 @
% 0.99/1.21           A @ 
% 0.99/1.21           ( k1_zfmisc_1 @
% 0.99/1.21             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.99/1.21  thf('64', plain,
% 0.99/1.21      (![X47 : $i]:
% 0.99/1.21         ((m1_subset_1 @ X47 @ 
% 0.99/1.21           (k1_zfmisc_1 @ 
% 0.99/1.21            (k2_zfmisc_1 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))))
% 0.99/1.21          | ~ (v1_funct_1 @ X47)
% 0.99/1.21          | ~ (v1_relat_1 @ X47))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.99/1.21  thf('65', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((m1_subset_1 @ sk_B_1 @ 
% 0.99/1.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0)))
% 0.99/1.21          | (zip_tseitin_0 @ sk_A @ X0)
% 0.99/1.21          | ~ (v1_relat_1 @ sk_B_1)
% 0.99/1.21          | ~ (v1_funct_1 @ sk_B_1))),
% 0.99/1.21      inference('sup+', [status(thm)], ['63', '64'])).
% 0.99/1.21  thf(t113_zfmisc_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.99/1.21       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.99/1.21  thf('66', plain,
% 0.99/1.21      (![X26 : $i, X27 : $i]:
% 0.99/1.21         (((k2_zfmisc_1 @ X26 @ X27) = (k1_xboole_0))
% 0.99/1.21          | ((X27) != (k1_xboole_0)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.99/1.21  thf('67', plain,
% 0.99/1.21      (![X26 : $i]: ((k2_zfmisc_1 @ X26 @ k1_xboole_0) = (k1_xboole_0))),
% 0.99/1.21      inference('simplify', [status(thm)], ['66'])).
% 0.99/1.21  thf('68', plain, ((v1_relat_1 @ sk_B_1)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('69', plain, ((v1_funct_1 @ sk_B_1)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('70', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.99/1.21          | (zip_tseitin_0 @ sk_A @ X0))),
% 0.99/1.21      inference('demod', [status(thm)], ['65', '67', '68', '69'])).
% 0.99/1.21  thf(t3_subset, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.21  thf('71', plain,
% 0.99/1.21      (![X28 : $i, X29 : $i]:
% 0.99/1.21         ((r1_tarski @ X28 @ X29) | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29)))),
% 0.99/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.21  thf('72', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X0) | (r1_tarski @ sk_B_1 @ k1_xboole_0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['70', '71'])).
% 0.99/1.21  thf('73', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 0.99/1.21      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.99/1.21  thf(t69_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]:
% 0.99/1.21     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.99/1.21       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.99/1.21  thf('74', plain,
% 0.99/1.21      (![X21 : $i, X22 : $i]:
% 0.99/1.21         (~ (r1_xboole_0 @ X21 @ X22)
% 0.99/1.21          | ~ (r1_tarski @ X21 @ X22)
% 0.99/1.21          | (v1_xboole_0 @ X21))),
% 0.99/1.21      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.99/1.21  thf('75', plain,
% 0.99/1.21      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['73', '74'])).
% 0.99/1.21  thf('76', plain,
% 0.99/1.21      (![X0 : $i]: ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ sk_B_1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['72', '75'])).
% 0.99/1.21  thf('77', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ (k3_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('clc', [status(thm)], ['62', '76'])).
% 0.99/1.21  thf('78', plain,
% 0.99/1.21      (![X31 : $i]:
% 0.99/1.21         (((k3_relat_1 @ X31)
% 0.99/1.21            = (k2_xboole_0 @ (k2_relat_1 @ X31) @ (k1_relat_1 @ X31)))
% 0.99/1.21          | ~ (v1_relat_1 @ X31))),
% 0.99/1.21      inference('demod', [status(thm)], ['52', '53'])).
% 0.99/1.21  thf('79', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.99/1.21      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.99/1.21  thf(t7_xboole_1, axiom,
% 0.99/1.21    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.99/1.21  thf('80', plain,
% 0.99/1.21      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 0.99/1.21      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.99/1.21  thf('81', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['79', '80'])).
% 0.99/1.21  thf('82', plain,
% 0.99/1.21      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 0.99/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.99/1.21  thf('83', plain,
% 0.99/1.21      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.99/1.21      inference('sup-', [status(thm)], ['73', '74'])).
% 0.99/1.21  thf('84', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         (~ (r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ X1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['82', '83'])).
% 0.99/1.21  thf('85', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['81', '84'])).
% 0.99/1.21  thf('86', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         (~ (v1_xboole_0 @ (k3_relat_1 @ X0))
% 0.99/1.21          | ~ (v1_relat_1 @ X0)
% 0.99/1.21          | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['78', '85'])).
% 0.99/1.21  thf('87', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X0)
% 0.99/1.21          | (v1_xboole_0 @ (k1_relat_1 @ sk_B_1))
% 0.99/1.21          | ~ (v1_relat_1 @ sk_B_1))),
% 0.99/1.21      inference('sup-', [status(thm)], ['77', '86'])).
% 0.99/1.21  thf('88', plain, ((v1_relat_1 @ sk_B_1)),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.21  thf('89', plain,
% 0.99/1.21      (![X0 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X0) | (v1_xboole_0 @ (k1_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('demod', [status(thm)], ['87', '88'])).
% 0.99/1.21  thf('90', plain,
% 0.99/1.21      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 0.99/1.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.99/1.21  thf('91', plain,
% 0.99/1.21      (![X39 : $i, X40 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 0.99/1.21      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.99/1.21  thf('92', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 0.99/1.21      inference('simplify', [status(thm)], ['91'])).
% 0.99/1.21  thf('93', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.21      inference('sup+', [status(thm)], ['90', '92'])).
% 0.99/1.21  thf('94', plain,
% 0.99/1.21      (![X0 : $i, X1 : $i]:
% 0.99/1.21         ((zip_tseitin_0 @ sk_A @ X1)
% 0.99/1.21          | (zip_tseitin_0 @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.99/1.21      inference('sup-', [status(thm)], ['89', '93'])).
% 0.99/1.21  thf('95', plain, ((zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.99/1.21      inference('eq_fact', [status(thm)], ['94'])).
% 0.99/1.21  thf('96', plain, ((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.99/1.21      inference('demod', [status(thm)], ['26', '95'])).
% 0.99/1.21  thf('97', plain, ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.99/1.21      inference('demod', [status(thm)], ['23', '96'])).
% 0.99/1.21  thf('98', plain, ($false), inference('demod', [status(thm)], ['17', '97'])).
% 0.99/1.21  
% 0.99/1.21  % SZS output end Refutation
% 0.99/1.21  
% 0.99/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

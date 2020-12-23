%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nz9VTqAYAM

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:42 EST 2020

% Result     : Theorem 30.49s
% Output     : Refutation 30.49s
% Verified   : 
% Statistics : Number of formulae       :  391 (2867 expanded)
%              Number of leaves         :   48 ( 887 expanded)
%              Depth                    :   44
%              Number of atoms          : 3206 (37086 expanded)
%              Number of equality atoms :  234 (1883 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

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

thf('12',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('16',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X20: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('34',plain,
    ( ( ( k10_relat_1 @ sk_C_1 @ sk_B )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('36',plain,
    ( ( k10_relat_1 @ sk_C_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('39',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B = X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('58',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('59',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('60',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X21 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_B != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','68'])).

thf('70',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('74',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('76',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('80',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['78','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('85',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('89',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','90'])).

thf('92',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('94',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','101'])).

thf('103',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( X0 = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k2_funct_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','108'])).

thf('110',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('112',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('114',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('115',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('118',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C_1 @ X0 ) @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C_1 @ X0 ) @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['36','121'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('123',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('124',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['27','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','90'])).

thf('131',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( X0
        = ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('136',plain,
    ( ( ~ ( v1_funct_2 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ~ ( v1_funct_2 @ sk_A @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('139',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k2_funct_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('145',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('147',plain,(
    ! [X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X21 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('148',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['145','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('152',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('156',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( zip_tseitin_1 @ X2 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('162',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k1_relset_1 @ X28 @ X29 @ X27 )
        = ( k1_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( X35
       != ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ X2 )
      | ( v1_funct_2 @ X0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['160','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_B = X0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('170',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('173',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ X0 @ sk_A )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['168','173'])).

thf('175',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['153','174'])).

thf('176',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('177',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( v1_xboole_0 @ sk_A )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('182',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('184',plain,(
    r1_tarski @ sk_C_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('186',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['181','186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['180','187'])).

thf('189',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C_1 ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('192',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('193',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('195',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('198',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['190','198'])).

thf('200',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup+',[status(thm)],['179','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('202',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['181','186'])).

thf('205',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('207',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['200','207'])).

thf('209',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('210',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('212',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('213',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['211','213'])).

thf('215',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('216',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','217'])).

thf('219',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['210','218'])).

thf('220',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('221',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['178','221'])).

thf('223',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['144','222'])).

thf('224',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( ~ ( v1_xboole_0 @ sk_C_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['143','224'])).

thf('226',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['142','226'])).

thf('228',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['139','228'])).

thf('230',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('231',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('232',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('233',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('234',plain,(
    ! [X41: $i] :
      ( ( v1_funct_2 @ X41 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['232','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['231','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['230','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['229','241'])).

thf('243',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('244',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('245',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['242','243','244','245','246'])).

thf('248',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','247'])).

thf('249',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('250',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','248','249'])).

thf('251',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','250'])).

thf('252',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('253',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('254',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('255',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('256',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('257',plain,(
    ! [X20: $i] :
      ( ( ( k10_relat_1 @ X20 @ ( k2_relat_1 @ X20 ) )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('258',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('259',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('260',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('261',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['259','262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['258','264'])).

thf('266',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('267',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 ) @ sk_B ) ),
    inference(demod,[status(thm)],['265','266','267','268'])).

thf('270',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['257','269'])).

thf('271',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['256','270'])).

thf('272',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('273',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_B ),
    inference(demod,[status(thm)],['271','272','273'])).

thf('275',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('276',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['274','275'])).

thf('277',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['255','276'])).

thf('278',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('279',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('280',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['279'])).

thf('281',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('282',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['277','278','280','281','282','283'])).

thf('285',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('286',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['284','285'])).

thf('287',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['254','286'])).

thf('288',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('289',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('290',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['287','288','289'])).

thf('291',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['253','290'])).

thf('292',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('293',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['291','292','293'])).

thf('295',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['252','294'])).

thf('296',plain,(
    ! [X22: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('297',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('298',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('300',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('301',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['300'])).

thf('302',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['299','301'])).

thf('303',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X41 ) @ ( k2_relat_1 @ X41 ) ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('304',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('305',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('306',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['300'])).

thf('307',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['305','306'])).

thf('308',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('309',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['307','308'])).

thf('310',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('311',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['309','310'])).

thf('312',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('313',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['304','313'])).

thf('315',plain,
    ( ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['303','314'])).

thf('316',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['302','315'])).

thf('317',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('318',plain,
    ( ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['298','318'])).

thf('320',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('321',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('322',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['319','320','321','322','323'])).

thf('325',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['297','324'])).

thf('326',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('327',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('328',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['325','326','327'])).

thf('329',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('330',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['296','330'])).

thf('332',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('333',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['331','332','333'])).

thf('335',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','248','249'])).

thf('336',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['334','335'])).

thf('337',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('338',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('339',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['295','336','337','338','339'])).

thf('341',plain,(
    $false ),
    inference(demod,[status(thm)],['251','340'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Nz9VTqAYAM
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:26:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 30.49/30.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 30.49/30.70  % Solved by: fo/fo7.sh
% 30.49/30.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 30.49/30.70  % done 22253 iterations in 30.229s
% 30.49/30.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 30.49/30.70  % SZS output start Refutation
% 30.49/30.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 30.49/30.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 30.49/30.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 30.49/30.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 30.49/30.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 30.49/30.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 30.49/30.70  thf(sk_A_type, type, sk_A: $i).
% 30.49/30.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 30.49/30.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 30.49/30.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 30.49/30.70  thf(sk_B_type, type, sk_B: $i).
% 30.49/30.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 30.49/30.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 30.49/30.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 30.49/30.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 30.49/30.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 30.49/30.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 30.49/30.70  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 30.49/30.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 30.49/30.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 30.49/30.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 30.49/30.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 30.49/30.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 30.49/30.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 30.49/30.70  thf(t31_funct_2, conjecture,
% 30.49/30.70    (![A:$i,B:$i,C:$i]:
% 30.49/30.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.49/30.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.49/30.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 30.49/30.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 30.49/30.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 30.49/30.70           ( m1_subset_1 @
% 30.49/30.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 30.49/30.70  thf(zf_stmt_0, negated_conjecture,
% 30.49/30.70    (~( ![A:$i,B:$i,C:$i]:
% 30.49/30.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 30.49/30.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 30.49/30.70          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 30.49/30.70            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 30.49/30.70              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 30.49/30.70              ( m1_subset_1 @
% 30.49/30.70                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 30.49/30.70    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 30.49/30.70  thf('0', plain,
% 30.49/30.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 30.49/30.70        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('1', plain,
% 30.49/30.70      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 30.49/30.70         <= (~
% 30.49/30.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.70      inference('split', [status(esa)], ['0'])).
% 30.49/30.70  thf('2', plain,
% 30.49/30.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf(cc1_relset_1, axiom,
% 30.49/30.70    (![A:$i,B:$i,C:$i]:
% 30.49/30.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.49/30.70       ( v1_relat_1 @ C ) ))).
% 30.49/30.70  thf('3', plain,
% 30.49/30.70      (![X24 : $i, X25 : $i, X26 : $i]:
% 30.49/30.70         ((v1_relat_1 @ X24)
% 30.49/30.70          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 30.49/30.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 30.49/30.70  thf('4', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf(dt_k2_funct_1, axiom,
% 30.49/30.70    (![A:$i]:
% 30.49/30.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.49/30.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 30.49/30.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 30.49/30.70  thf('5', plain,
% 30.49/30.70      (![X22 : $i]:
% 30.49/30.70         ((v1_funct_1 @ (k2_funct_1 @ X22))
% 30.49/30.70          | ~ (v1_funct_1 @ X22)
% 30.49/30.70          | ~ (v1_relat_1 @ X22))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.70  thf('6', plain,
% 30.49/30.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 30.49/30.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 30.49/30.70      inference('split', [status(esa)], ['0'])).
% 30.49/30.70  thf('7', plain,
% 30.49/30.70      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 30.49/30.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 30.49/30.70      inference('sup-', [status(thm)], ['5', '6'])).
% 30.49/30.70  thf('8', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('9', plain,
% 30.49/30.70      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 30.49/30.70      inference('demod', [status(thm)], ['7', '8'])).
% 30.49/30.70  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['4', '9'])).
% 30.49/30.70  thf('11', plain,
% 30.49/30.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('split', [status(esa)], ['0'])).
% 30.49/30.70  thf(d1_funct_2, axiom,
% 30.49/30.70    (![A:$i,B:$i,C:$i]:
% 30.49/30.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.49/30.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.49/30.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 30.49/30.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 30.49/30.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.49/30.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 30.49/30.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 30.49/30.70  thf(zf_stmt_1, axiom,
% 30.49/30.70    (![B:$i,A:$i]:
% 30.49/30.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 30.49/30.70       ( zip_tseitin_0 @ B @ A ) ))).
% 30.49/30.70  thf('12', plain,
% 30.49/30.70      (![X33 : $i, X34 : $i]:
% 30.49/30.70         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.49/30.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 30.49/30.70  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('14', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 30.49/30.70      inference('sup+', [status(thm)], ['12', '13'])).
% 30.49/30.70  thf('15', plain,
% 30.49/30.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 30.49/30.70  thf(zf_stmt_3, axiom,
% 30.49/30.70    (![C:$i,B:$i,A:$i]:
% 30.49/30.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 30.49/30.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 30.49/30.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 30.49/30.70  thf(zf_stmt_5, axiom,
% 30.49/30.70    (![A:$i,B:$i,C:$i]:
% 30.49/30.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.49/30.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 30.49/30.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 30.49/30.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 30.49/30.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 30.49/30.70  thf('16', plain,
% 30.49/30.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 30.49/30.70         (~ (zip_tseitin_0 @ X38 @ X39)
% 30.49/30.70          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 30.49/30.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.49/30.70  thf('17', plain,
% 30.49/30.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.49/30.70      inference('sup-', [status(thm)], ['15', '16'])).
% 30.49/30.70  thf('18', plain,
% 30.49/30.70      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.70      inference('sup-', [status(thm)], ['14', '17'])).
% 30.49/30.70  thf('19', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('20', plain,
% 30.49/30.70      (![X35 : $i, X36 : $i, X37 : $i]:
% 30.49/30.70         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 30.49/30.70          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 30.49/30.70          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 30.49/30.70  thf('21', plain,
% 30.49/30.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['19', '20'])).
% 30.49/30.70  thf('22', plain,
% 30.49/30.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf(redefinition_k1_relset_1, axiom,
% 30.49/30.70    (![A:$i,B:$i,C:$i]:
% 30.49/30.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.49/30.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 30.49/30.70  thf('23', plain,
% 30.49/30.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.49/30.70         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 30.49/30.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 30.49/30.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 30.49/30.70  thf('24', plain,
% 30.49/30.70      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['22', '23'])).
% 30.49/30.70  thf('25', plain,
% 30.49/30.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['21', '24'])).
% 30.49/30.70  thf('26', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['18', '25'])).
% 30.49/30.70  thf(d3_tarski, axiom,
% 30.49/30.70    (![A:$i,B:$i]:
% 30.49/30.70     ( ( r1_tarski @ A @ B ) <=>
% 30.49/30.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 30.49/30.70  thf('27', plain,
% 30.49/30.70      (![X1 : $i, X3 : $i]:
% 30.49/30.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 30.49/30.70      inference('cnf', [status(esa)], [d3_tarski])).
% 30.49/30.70  thf('28', plain,
% 30.49/30.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf(redefinition_k2_relset_1, axiom,
% 30.49/30.70    (![A:$i,B:$i,C:$i]:
% 30.49/30.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 30.49/30.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 30.49/30.70  thf('29', plain,
% 30.49/30.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 30.49/30.70         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 30.49/30.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 30.49/30.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 30.49/30.70  thf('30', plain,
% 30.49/30.70      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['28', '29'])).
% 30.49/30.70  thf('31', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('32', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.70      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.70  thf(t169_relat_1, axiom,
% 30.49/30.70    (![A:$i]:
% 30.49/30.70     ( ( v1_relat_1 @ A ) =>
% 30.49/30.70       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 30.49/30.70  thf('33', plain,
% 30.49/30.70      (![X20 : $i]:
% 30.49/30.70         (((k10_relat_1 @ X20 @ (k2_relat_1 @ X20)) = (k1_relat_1 @ X20))
% 30.49/30.70          | ~ (v1_relat_1 @ X20))),
% 30.49/30.70      inference('cnf', [status(esa)], [t169_relat_1])).
% 30.49/30.70  thf('34', plain,
% 30.49/30.70      ((((k10_relat_1 @ sk_C_1 @ sk_B) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ~ (v1_relat_1 @ sk_C_1))),
% 30.49/30.70      inference('sup+', [status(thm)], ['32', '33'])).
% 30.49/30.70  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('36', plain, (((k10_relat_1 @ sk_C_1 @ sk_B) = (k1_relat_1 @ sk_C_1))),
% 30.49/30.70      inference('demod', [status(thm)], ['34', '35'])).
% 30.49/30.70  thf('37', plain,
% 30.49/30.70      (![X1 : $i, X3 : $i]:
% 30.49/30.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 30.49/30.70      inference('cnf', [status(esa)], [d3_tarski])).
% 30.49/30.70  thf('38', plain,
% 30.49/30.70      (![X22 : $i]:
% 30.49/30.70         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.70          | ~ (v1_funct_1 @ X22)
% 30.49/30.70          | ~ (v1_relat_1 @ X22))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.70  thf('39', plain,
% 30.49/30.70      (![X22 : $i]:
% 30.49/30.70         ((v1_funct_1 @ (k2_funct_1 @ X22))
% 30.49/30.70          | ~ (v1_funct_1 @ X22)
% 30.49/30.70          | ~ (v1_relat_1 @ X22))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.70  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('41', plain,
% 30.49/30.70      (![X1 : $i, X3 : $i]:
% 30.49/30.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 30.49/30.70      inference('cnf', [status(esa)], [d3_tarski])).
% 30.49/30.70  thf(dt_k2_subset_1, axiom,
% 30.49/30.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 30.49/30.70  thf('42', plain,
% 30.49/30.70      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 30.49/30.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 30.49/30.70  thf('43', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 30.49/30.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 30.49/30.70  thf('44', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 30.49/30.70      inference('demod', [status(thm)], ['42', '43'])).
% 30.49/30.70  thf(t5_subset, axiom,
% 30.49/30.70    (![A:$i,B:$i,C:$i]:
% 30.49/30.70     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 30.49/30.70          ( v1_xboole_0 @ C ) ) ))).
% 30.49/30.70  thf('45', plain,
% 30.49/30.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.49/30.70         (~ (r2_hidden @ X15 @ X16)
% 30.49/30.70          | ~ (v1_xboole_0 @ X17)
% 30.49/30.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 30.49/30.70      inference('cnf', [status(esa)], [t5_subset])).
% 30.49/30.70  thf('46', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['44', '45'])).
% 30.49/30.70  thf('47', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['41', '46'])).
% 30.49/30.70  thf('48', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['41', '46'])).
% 30.49/30.70  thf(d10_xboole_0, axiom,
% 30.49/30.70    (![A:$i,B:$i]:
% 30.49/30.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 30.49/30.70  thf('49', plain,
% 30.49/30.70      (![X4 : $i, X6 : $i]:
% 30.49/30.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 30.49/30.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.49/30.70  thf('50', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['48', '49'])).
% 30.49/30.70  thf('51', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['47', '50'])).
% 30.49/30.70  thf('52', plain,
% 30.49/30.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['40', '51'])).
% 30.49/30.70  thf('53', plain,
% 30.49/30.70      (![X33 : $i, X34 : $i]:
% 30.49/30.70         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.49/30.70  thf('54', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.70         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 30.49/30.70      inference('sup+', [status(thm)], ['52', '53'])).
% 30.49/30.70  thf('55', plain,
% 30.49/30.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.49/30.70      inference('sup-', [status(thm)], ['15', '16'])).
% 30.49/30.70  thf('56', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X0)
% 30.49/30.70          | ((sk_B) = (X0))
% 30.49/30.70          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.70      inference('sup-', [status(thm)], ['54', '55'])).
% 30.49/30.70  thf('57', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.70      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.70  thf('58', plain,
% 30.49/30.70      (![X22 : $i]:
% 30.49/30.70         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.70          | ~ (v1_funct_1 @ X22)
% 30.49/30.70          | ~ (v1_relat_1 @ X22))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.70  thf(t55_funct_1, axiom,
% 30.49/30.70    (![A:$i]:
% 30.49/30.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.49/30.70       ( ( v2_funct_1 @ A ) =>
% 30.49/30.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 30.49/30.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 30.49/30.70  thf('59', plain,
% 30.49/30.70      (![X23 : $i]:
% 30.49/30.70         (~ (v2_funct_1 @ X23)
% 30.49/30.70          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.70          | ~ (v1_funct_1 @ X23)
% 30.49/30.70          | ~ (v1_relat_1 @ X23))),
% 30.49/30.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.70  thf(t65_relat_1, axiom,
% 30.49/30.70    (![A:$i]:
% 30.49/30.70     ( ( v1_relat_1 @ A ) =>
% 30.49/30.70       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 30.49/30.70         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 30.49/30.70  thf('60', plain,
% 30.49/30.70      (![X21 : $i]:
% 30.49/30.70         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 30.49/30.70          | ((k2_relat_1 @ X21) = (k1_xboole_0))
% 30.49/30.70          | ~ (v1_relat_1 @ X21))),
% 30.49/30.70      inference('cnf', [status(esa)], [t65_relat_1])).
% 30.49/30.70  thf('61', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 30.49/30.70          | ~ (v1_relat_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v2_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 30.49/30.70          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['59', '60'])).
% 30.49/30.70  thf('62', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_relat_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0))
% 30.49/30.70          | ~ (v2_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_relat_1 @ X0)
% 30.49/30.70          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['58', '61'])).
% 30.49/30.70  thf('63', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 30.49/30.70          | ~ (v2_funct_1 @ X0)
% 30.49/30.70          | ((k2_relat_1 @ (k2_funct_1 @ X0)) = (k1_xboole_0))
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_relat_1 @ X0))),
% 30.49/30.70      inference('simplify', [status(thm)], ['62'])).
% 30.49/30.70  thf('64', plain,
% 30.49/30.70      ((((sk_B) != (k1_xboole_0))
% 30.49/30.70        | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.70        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0))
% 30.49/30.70        | ~ (v2_funct_1 @ sk_C_1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['57', '63'])).
% 30.49/30.70  thf('65', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('67', plain, ((v2_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('68', plain,
% 30.49/30.70      ((((sk_B) != (k1_xboole_0))
% 30.49/30.70        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0)))),
% 30.49/30.70      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 30.49/30.70  thf('69', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((X0) != (k1_xboole_0))
% 30.49/30.70          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70          | ~ (v1_xboole_0 @ X0)
% 30.49/30.70          | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['56', '68'])).
% 30.49/30.70  thf('70', plain,
% 30.49/30.70      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0))
% 30.49/30.70        | ~ (v1_xboole_0 @ k1_xboole_0)
% 30.49/30.70        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.70      inference('simplify', [status(thm)], ['69'])).
% 30.49/30.70  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('72', plain,
% 30.49/30.70      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0))
% 30.49/30.70        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.70      inference('simplify_reflect+', [status(thm)], ['70', '71'])).
% 30.49/30.70  thf('73', plain,
% 30.49/30.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['21', '24'])).
% 30.49/30.70  thf('74', plain,
% 30.49/30.70      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['72', '73'])).
% 30.49/30.70  thf(t3_funct_2, axiom,
% 30.49/30.70    (![A:$i]:
% 30.49/30.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 30.49/30.70       ( ( v1_funct_1 @ A ) & 
% 30.49/30.70         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 30.49/30.70         ( m1_subset_1 @
% 30.49/30.70           A @ 
% 30.49/30.70           ( k1_zfmisc_1 @
% 30.49/30.70             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 30.49/30.70  thf('75', plain,
% 30.49/30.70      (![X41 : $i]:
% 30.49/30.70         ((m1_subset_1 @ X41 @ 
% 30.49/30.70           (k1_zfmisc_1 @ 
% 30.49/30.70            (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41))))
% 30.49/30.70          | ~ (v1_funct_1 @ X41)
% 30.49/30.70          | ~ (v1_relat_1 @ X41))),
% 30.49/30.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 30.49/30.70  thf('76', plain,
% 30.49/30.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.49/30.70         (~ (r2_hidden @ X15 @ X16)
% 30.49/30.70          | ~ (v1_xboole_0 @ X17)
% 30.49/30.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 30.49/30.70      inference('cnf', [status(esa)], [t5_subset])).
% 30.49/30.70  thf('77', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_relat_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_xboole_0 @ 
% 30.49/30.70               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 30.49/30.70          | ~ (r2_hidden @ X1 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['75', '76'])).
% 30.49/30.70  thf('78', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ 
% 30.49/30.70             (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ k1_xboole_0))
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['74', '77'])).
% 30.49/30.70  thf(t113_zfmisc_1, axiom,
% 30.49/30.70    (![A:$i,B:$i]:
% 30.49/30.70     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 30.49/30.70       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 30.49/30.70  thf('79', plain,
% 30.49/30.70      (![X8 : $i, X9 : $i]:
% 30.49/30.70         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 30.49/30.70      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 30.49/30.70  thf('80', plain,
% 30.49/30.70      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 30.49/30.70      inference('simplify', [status(thm)], ['79'])).
% 30.49/30.70  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('82', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['78', '80', '81'])).
% 30.49/30.70  thf('83', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_relat_1 @ sk_C_1)
% 30.49/30.70          | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['39', '82'])).
% 30.49/30.70  thf('84', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('85', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('86', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['83', '84', '85'])).
% 30.49/30.70  thf('87', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_relat_1 @ sk_C_1)
% 30.49/30.70          | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['38', '86'])).
% 30.49/30.70  thf('88', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('89', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('90', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (r2_hidden @ X0 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['87', '88', '89'])).
% 30.49/30.70  thf('91', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ (k2_funct_1 @ sk_C_1) @ X0)
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['37', '90'])).
% 30.49/30.70  thf('92', plain,
% 30.49/30.70      (![X1 : $i, X3 : $i]:
% 30.49/30.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 30.49/30.70      inference('cnf', [status(esa)], [d3_tarski])).
% 30.49/30.70  thf('93', plain,
% 30.49/30.70      (![X33 : $i, X34 : $i]:
% 30.49/30.70         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.49/30.70  thf('94', plain,
% 30.49/30.70      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 30.49/30.70      inference('simplify', [status(thm)], ['79'])).
% 30.49/30.70  thf('95', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.70         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 30.49/30.70      inference('sup+', [status(thm)], ['93', '94'])).
% 30.49/30.70  thf('96', plain,
% 30.49/30.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('97', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 30.49/30.70          | (zip_tseitin_0 @ sk_B @ X0))),
% 30.49/30.70      inference('sup+', [status(thm)], ['95', '96'])).
% 30.49/30.70  thf('98', plain,
% 30.49/30.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.49/30.70         (~ (r2_hidden @ X15 @ X16)
% 30.49/30.70          | ~ (v1_xboole_0 @ X17)
% 30.49/30.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 30.49/30.70      inference('cnf', [status(esa)], [t5_subset])).
% 30.49/30.70  thf('99', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         ((zip_tseitin_0 @ sk_B @ X1)
% 30.49/30.70          | ~ (v1_xboole_0 @ k1_xboole_0)
% 30.49/30.70          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['97', '98'])).
% 30.49/30.70  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('101', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         ((zip_tseitin_0 @ sk_B @ X1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 30.49/30.70      inference('demod', [status(thm)], ['99', '100'])).
% 30.49/30.70  thf('102', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         ((r1_tarski @ sk_C_1 @ X0) | (zip_tseitin_0 @ sk_B @ X1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['92', '101'])).
% 30.49/30.70  thf('103', plain,
% 30.49/30.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.49/30.70      inference('sup-', [status(thm)], ['15', '16'])).
% 30.49/30.70  thf('104', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ sk_C_1 @ X0) | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.70      inference('sup-', [status(thm)], ['102', '103'])).
% 30.49/30.70  thf('105', plain,
% 30.49/30.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['21', '24'])).
% 30.49/30.70  thf('106', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ sk_C_1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['104', '105'])).
% 30.49/30.70  thf('107', plain,
% 30.49/30.70      (![X4 : $i, X6 : $i]:
% 30.49/30.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 30.49/30.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.49/30.70  thf('108', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (r1_tarski @ X0 @ sk_C_1)
% 30.49/30.70          | ((X0) = (sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['106', '107'])).
% 30.49/30.70  thf('109', plain,
% 30.49/30.70      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ((k2_funct_1 @ sk_C_1) = (sk_C_1))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['91', '108'])).
% 30.49/30.70  thf('110', plain,
% 30.49/30.70      ((((k2_funct_1 @ sk_C_1) = (sk_C_1)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['109'])).
% 30.49/30.70  thf('111', plain,
% 30.49/30.70      (![X23 : $i]:
% 30.49/30.70         (~ (v2_funct_1 @ X23)
% 30.49/30.70          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.70          | ~ (v1_funct_1 @ X23)
% 30.49/30.70          | ~ (v1_relat_1 @ X23))),
% 30.49/30.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.70  thf('112', plain,
% 30.49/30.70      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.70        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.70        | ~ (v2_funct_1 @ sk_C_1))),
% 30.49/30.70      inference('sup+', [status(thm)], ['110', '111'])).
% 30.49/30.70  thf('113', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.70      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.70  thf('114', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('115', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('116', plain, ((v2_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('117', plain,
% 30.49/30.70      ((((k1_relat_1 @ sk_C_1) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 30.49/30.70  thf(t167_relat_1, axiom,
% 30.49/30.70    (![A:$i,B:$i]:
% 30.49/30.70     ( ( v1_relat_1 @ B ) =>
% 30.49/30.70       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 30.49/30.70  thf('118', plain,
% 30.49/30.70      (![X18 : $i, X19 : $i]:
% 30.49/30.70         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 30.49/30.70          | ~ (v1_relat_1 @ X18))),
% 30.49/30.70      inference('cnf', [status(esa)], [t167_relat_1])).
% 30.49/30.70  thf('119', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ (k10_relat_1 @ sk_C_1 @ X0) @ sk_B)
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (v1_relat_1 @ sk_C_1))),
% 30.49/30.70      inference('sup+', [status(thm)], ['117', '118'])).
% 30.49/30.70  thf('120', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('121', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ (k10_relat_1 @ sk_C_1 @ X0) @ sk_B)
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['119', '120'])).
% 30.49/30.70  thf('122', plain,
% 30.49/30.70      (((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup+', [status(thm)], ['36', '121'])).
% 30.49/30.70  thf(t3_subset, axiom,
% 30.49/30.70    (![A:$i,B:$i]:
% 30.49/30.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 30.49/30.70  thf('123', plain,
% 30.49/30.70      (![X12 : $i, X14 : $i]:
% 30.49/30.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 30.49/30.70      inference('cnf', [status(esa)], [t3_subset])).
% 30.49/30.70  thf('124', plain,
% 30.49/30.70      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | (m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['122', '123'])).
% 30.49/30.70  thf('125', plain,
% 30.49/30.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 30.49/30.70         (~ (r2_hidden @ X15 @ X16)
% 30.49/30.70          | ~ (v1_xboole_0 @ X17)
% 30.49/30.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 30.49/30.70      inference('cnf', [status(esa)], [t5_subset])).
% 30.49/30.70  thf('126', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (v1_xboole_0 @ sk_B)
% 30.49/30.70          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['124', '125'])).
% 30.49/30.70  thf('127', plain,
% 30.49/30.70      (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['18', '25'])).
% 30.49/30.70  thf('128', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('clc', [status(thm)], ['126', '127'])).
% 30.49/30.70  thf('129', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0)
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['27', '128'])).
% 30.49/30.70  thf('130', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ (k2_funct_1 @ sk_C_1) @ X0)
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['37', '90'])).
% 30.49/30.70  thf('131', plain,
% 30.49/30.70      (![X4 : $i, X6 : $i]:
% 30.49/30.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 30.49/30.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.49/30.70  thf('132', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ~ (r1_tarski @ X0 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70          | ((X0) = (k2_funct_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['130', '131'])).
% 30.49/30.70  thf('133', plain,
% 30.49/30.70      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ((k1_relat_1 @ sk_C_1) = (k2_funct_1 @ sk_C_1))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['129', '132'])).
% 30.49/30.70  thf('134', plain,
% 30.49/30.70      ((((k1_relat_1 @ sk_C_1) = (k2_funct_1 @ sk_C_1))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['133'])).
% 30.49/30.70  thf('135', plain,
% 30.49/30.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('split', [status(esa)], ['0'])).
% 30.49/30.70  thf('136', plain,
% 30.49/30.70      (((~ (v1_funct_2 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_A)
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['134', '135'])).
% 30.49/30.70  thf('137', plain,
% 30.49/30.70      (((~ (v1_funct_2 @ sk_A @ sk_B @ sk_A)
% 30.49/30.70         | (v1_xboole_0 @ sk_B)
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['26', '136'])).
% 30.49/30.70  thf('138', plain,
% 30.49/30.70      (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['18', '25'])).
% 30.49/30.70  thf('139', plain,
% 30.49/30.70      (((((sk_A) = (k1_relat_1 @ sk_C_1)) | (v1_xboole_0 @ sk_B)))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('clc', [status(thm)], ['137', '138'])).
% 30.49/30.70  thf('140', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((r1_tarski @ sk_C_1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['104', '105'])).
% 30.49/30.70  thf('141', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['48', '49'])).
% 30.49/30.70  thf('142', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ((sk_C_1) = (X0))
% 30.49/30.70          | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['140', '141'])).
% 30.49/30.70  thf('143', plain,
% 30.49/30.70      ((((k2_funct_1 @ sk_C_1) = (sk_C_1)) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['109'])).
% 30.49/30.70  thf('144', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70          | ((sk_C_1) = (X0))
% 30.49/30.70          | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['140', '141'])).
% 30.49/30.70  thf('145', plain,
% 30.49/30.70      (![X22 : $i]:
% 30.49/30.70         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.70          | ~ (v1_funct_1 @ X22)
% 30.49/30.70          | ~ (v1_relat_1 @ X22))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.70  thf('146', plain,
% 30.49/30.70      ((((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['72', '73'])).
% 30.49/30.70  thf('147', plain,
% 30.49/30.70      (![X21 : $i]:
% 30.49/30.70         (((k2_relat_1 @ X21) != (k1_xboole_0))
% 30.49/30.70          | ((k1_relat_1 @ X21) = (k1_xboole_0))
% 30.49/30.70          | ~ (v1_relat_1 @ X21))),
% 30.49/30.70      inference('cnf', [status(esa)], [t65_relat_1])).
% 30.49/30.70  thf('148', plain,
% 30.49/30.70      ((((k1_xboole_0) != (k1_xboole_0))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['146', '147'])).
% 30.49/30.70  thf('149', plain,
% 30.49/30.70      ((((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0))
% 30.49/30.70        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['148'])).
% 30.49/30.70  thf('150', plain,
% 30.49/30.70      ((~ (v1_relat_1 @ sk_C_1)
% 30.49/30.70        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['145', '149'])).
% 30.49/30.70  thf('151', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('152', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('153', plain,
% 30.49/30.70      ((((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k1_xboole_0)))),
% 30.49/30.70      inference('demod', [status(thm)], ['150', '151', '152'])).
% 30.49/30.70  thf('154', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 30.49/30.70      inference('sup+', [status(thm)], ['12', '13'])).
% 30.49/30.70  thf('155', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['41', '46'])).
% 30.49/30.70  thf('156', plain,
% 30.49/30.70      (![X12 : $i, X14 : $i]:
% 30.49/30.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 30.49/30.70      inference('cnf', [status(esa)], [t3_subset])).
% 30.49/30.70  thf('157', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['155', '156'])).
% 30.49/30.70  thf('158', plain,
% 30.49/30.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 30.49/30.70         (~ (zip_tseitin_0 @ X38 @ X39)
% 30.49/30.70          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 30.49/30.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.49/30.70  thf('159', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X2)
% 30.49/30.70          | (zip_tseitin_1 @ X2 @ X0 @ X1)
% 30.49/30.70          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['157', '158'])).
% 30.49/30.70  thf('160', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.70         ((v1_xboole_0 @ X1)
% 30.49/30.70          | (zip_tseitin_1 @ X2 @ X1 @ X0)
% 30.49/30.70          | ~ (v1_xboole_0 @ X2))),
% 30.49/30.70      inference('sup-', [status(thm)], ['154', '159'])).
% 30.49/30.70  thf('161', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['155', '156'])).
% 30.49/30.70  thf('162', plain,
% 30.49/30.70      (![X27 : $i, X28 : $i, X29 : $i]:
% 30.49/30.70         (((k1_relset_1 @ X28 @ X29 @ X27) = (k1_relat_1 @ X27))
% 30.49/30.70          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 30.49/30.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 30.49/30.70  thf('163', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X2)
% 30.49/30.70          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['161', '162'])).
% 30.49/30.70  thf('164', plain,
% 30.49/30.70      (![X35 : $i, X36 : $i, X37 : $i]:
% 30.49/30.70         (((X35) != (k1_relset_1 @ X35 @ X36 @ X37))
% 30.49/30.70          | (v1_funct_2 @ X37 @ X35 @ X36)
% 30.49/30.70          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 30.49/30.70  thf('165', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.70         (((X2) != (k1_relat_1 @ X0))
% 30.49/30.70          | ~ (v1_xboole_0 @ X0)
% 30.49/30.70          | ~ (zip_tseitin_1 @ X0 @ X1 @ X2)
% 30.49/30.70          | (v1_funct_2 @ X0 @ X2 @ X1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['163', '164'])).
% 30.49/30.70  thf('166', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1)
% 30.49/30.70          | ~ (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 30.49/30.70          | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('simplify', [status(thm)], ['165'])).
% 30.49/30.70  thf('167', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X0)
% 30.49/30.70          | (v1_xboole_0 @ X1)
% 30.49/30.70          | ~ (v1_xboole_0 @ X0)
% 30.49/30.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['160', '166'])).
% 30.49/30.70  thf('168', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1)
% 30.49/30.70          | (v1_xboole_0 @ X1)
% 30.49/30.70          | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('simplify', [status(thm)], ['167'])).
% 30.49/30.70  thf('169', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X0)
% 30.49/30.70          | ((sk_B) = (X0))
% 30.49/30.70          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.70      inference('sup-', [status(thm)], ['54', '55'])).
% 30.49/30.70  thf('170', plain,
% 30.49/30.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['21', '24'])).
% 30.49/30.70  thf('171', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (((sk_B) = (X0))
% 30.49/30.70          | ~ (v1_xboole_0 @ X0)
% 30.49/30.70          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['169', '170'])).
% 30.49/30.70  thf('172', plain,
% 30.49/30.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('split', [status(esa)], ['0'])).
% 30.49/30.70  thf('173', plain,
% 30.49/30.70      ((![X0 : $i]:
% 30.49/30.70          (~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ X0 @ sk_A)
% 30.49/30.70           | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70           | ~ (v1_xboole_0 @ X0)))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['171', '172'])).
% 30.49/30.70  thf('174', plain,
% 30.49/30.70      (((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70         | (v1_xboole_0 @ sk_A)
% 30.49/30.70         | ~ (v1_xboole_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['168', '173'])).
% 30.49/30.70  thf('175', plain,
% 30.49/30.70      (((~ (v1_xboole_0 @ k1_xboole_0)
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70         | (v1_xboole_0 @ sk_A)
% 30.49/30.70         | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['153', '174'])).
% 30.49/30.70  thf('176', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('177', plain,
% 30.49/30.70      (((((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70         | (v1_xboole_0 @ sk_A)
% 30.49/30.70         | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('demod', [status(thm)], ['175', '176'])).
% 30.49/30.70  thf('178', plain,
% 30.49/30.70      (((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.70         | (v1_xboole_0 @ sk_A)
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['177'])).
% 30.49/30.70  thf('179', plain,
% 30.49/30.70      (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['18', '25'])).
% 30.49/30.70  thf('180', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.70         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 30.49/30.70      inference('sup+', [status(thm)], ['93', '94'])).
% 30.49/30.70  thf('181', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['41', '46'])).
% 30.49/30.70  thf('182', plain,
% 30.49/30.70      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('183', plain,
% 30.49/30.70      (![X12 : $i, X13 : $i]:
% 30.49/30.70         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 30.49/30.70      inference('cnf', [status(esa)], [t3_subset])).
% 30.49/30.70  thf('184', plain, ((r1_tarski @ sk_C_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 30.49/30.70      inference('sup-', [status(thm)], ['182', '183'])).
% 30.49/30.70  thf('185', plain,
% 30.49/30.70      (![X4 : $i, X6 : $i]:
% 30.49/30.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 30.49/30.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.49/30.70  thf('186', plain,
% 30.49/30.70      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C_1)
% 30.49/30.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['184', '185'])).
% 30.49/30.70  thf('187', plain,
% 30.49/30.70      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 30.49/30.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['181', '186'])).
% 30.49/30.70  thf('188', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ k1_xboole_0)
% 30.49/30.70          | (zip_tseitin_0 @ sk_B @ X0)
% 30.49/30.70          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['180', '187'])).
% 30.49/30.70  thf('189', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('190', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((zip_tseitin_0 @ sk_B @ X0)
% 30.49/30.70          | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['188', '189'])).
% 30.49/30.70  thf('191', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.70      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.70  thf('192', plain,
% 30.49/30.70      (![X41 : $i]:
% 30.49/30.70         ((m1_subset_1 @ X41 @ 
% 30.49/30.70           (k1_zfmisc_1 @ 
% 30.49/30.70            (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41))))
% 30.49/30.70          | ~ (v1_funct_1 @ X41)
% 30.49/30.70          | ~ (v1_relat_1 @ X41))),
% 30.49/30.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 30.49/30.70  thf('193', plain,
% 30.49/30.70      (((m1_subset_1 @ sk_C_1 @ 
% 30.49/30.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))
% 30.49/30.70        | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.70        | ~ (v1_funct_1 @ sk_C_1))),
% 30.49/30.70      inference('sup+', [status(thm)], ['191', '192'])).
% 30.49/30.70  thf('194', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.70      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.70  thf('195', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.70  thf('196', plain,
% 30.49/30.70      ((m1_subset_1 @ sk_C_1 @ 
% 30.49/30.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 30.49/30.70      inference('demod', [status(thm)], ['193', '194', '195'])).
% 30.49/30.70  thf('197', plain,
% 30.49/30.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 30.49/30.70         (~ (zip_tseitin_0 @ X38 @ X39)
% 30.49/30.70          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 30.49/30.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.49/30.70  thf('198', plain,
% 30.49/30.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['196', '197'])).
% 30.49/30.70  thf('199', plain,
% 30.49/30.70      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1))
% 30.49/30.70        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['190', '198'])).
% 30.49/30.70  thf('200', plain,
% 30.49/30.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | (v1_xboole_0 @ sk_B)
% 30.49/30.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('sup+', [status(thm)], ['179', '199'])).
% 30.49/30.70  thf('201', plain,
% 30.49/30.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['40', '51'])).
% 30.49/30.70  thf('202', plain,
% 30.49/30.70      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 30.49/30.70      inference('simplify', [status(thm)], ['79'])).
% 30.49/30.70  thf('203', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup+', [status(thm)], ['201', '202'])).
% 30.49/30.70  thf('204', plain,
% 30.49/30.70      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 30.49/30.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['181', '186'])).
% 30.49/30.70  thf('205', plain,
% 30.49/30.70      ((~ (v1_xboole_0 @ k1_xboole_0)
% 30.49/30.70        | ~ (v1_xboole_0 @ sk_B)
% 30.49/30.70        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['203', '204'])).
% 30.49/30.70  thf('206', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.70  thf('207', plain,
% 30.49/30.70      ((~ (v1_xboole_0 @ sk_B) | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['205', '206'])).
% 30.49/30.70  thf('208', plain,
% 30.49/30.70      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1))
% 30.49/30.70        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.70      inference('clc', [status(thm)], ['200', '207'])).
% 30.49/30.70  thf('209', plain,
% 30.49/30.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['21', '24'])).
% 30.49/30.70  thf('210', plain,
% 30.49/30.70      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C_1))
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['208', '209'])).
% 30.49/30.70  thf('211', plain,
% 30.49/30.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['40', '51'])).
% 30.49/30.70  thf('212', plain,
% 30.49/30.70      (![X33 : $i, X34 : $i]:
% 30.49/30.70         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.49/30.70  thf('213', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 30.49/30.70      inference('simplify', [status(thm)], ['212'])).
% 30.49/30.70  thf('214', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.70      inference('sup+', [status(thm)], ['211', '213'])).
% 30.49/30.70  thf('215', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 30.49/30.70      inference('demod', [status(thm)], ['42', '43'])).
% 30.49/30.70  thf('216', plain,
% 30.49/30.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 30.49/30.70         (~ (zip_tseitin_0 @ X38 @ X39)
% 30.49/30.70          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 30.49/30.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 30.49/30.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 30.49/30.70  thf('217', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         ((zip_tseitin_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1)
% 30.49/30.70          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 30.49/30.70      inference('sup-', [status(thm)], ['215', '216'])).
% 30.49/30.70  thf('218', plain,
% 30.49/30.70      (![X0 : $i, X1 : $i]:
% 30.49/30.70         (~ (v1_xboole_0 @ X0)
% 30.49/30.70          | (zip_tseitin_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X1 @ X0))),
% 30.49/30.70      inference('sup-', [status(thm)], ['214', '217'])).
% 30.49/30.70  thf('219', plain,
% 30.49/30.70      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70        | ~ (v1_xboole_0 @ sk_A))),
% 30.49/30.70      inference('sup+', [status(thm)], ['210', '218'])).
% 30.49/30.70  thf('220', plain,
% 30.49/30.70      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.70        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('demod', [status(thm)], ['21', '24'])).
% 30.49/30.70  thf('221', plain,
% 30.49/30.70      ((~ (v1_xboole_0 @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.70      inference('clc', [status(thm)], ['219', '220'])).
% 30.49/30.70  thf('222', plain,
% 30.49/30.70      (((((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70         | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('clc', [status(thm)], ['178', '221'])).
% 30.49/30.70  thf('223', plain,
% 30.49/30.70      ((![X0 : $i]:
% 30.49/30.70          (~ (v1_xboole_0 @ (k2_funct_1 @ X0))
% 30.49/30.70           | ~ (v1_xboole_0 @ X0)
% 30.49/30.70           | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70           | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['144', '222'])).
% 30.49/30.70  thf('224', plain,
% 30.49/30.70      ((![X0 : $i]:
% 30.49/30.70          (((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70           | ~ (v1_xboole_0 @ X0)
% 30.49/30.70           | ~ (v1_xboole_0 @ (k2_funct_1 @ X0))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['223'])).
% 30.49/30.70  thf('225', plain,
% 30.49/30.70      (((~ (v1_xboole_0 @ sk_C_1)
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70         | ~ (v1_xboole_0 @ sk_C_1)
% 30.49/30.70         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['143', '224'])).
% 30.49/30.70  thf('226', plain,
% 30.49/30.70      (((((sk_A) = (k1_relat_1 @ sk_C_1)) | ~ (v1_xboole_0 @ sk_C_1)))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['225'])).
% 30.49/30.70  thf('227', plain,
% 30.49/30.70      ((![X0 : $i]:
% 30.49/30.70          (~ (v1_xboole_0 @ X0)
% 30.49/30.70           | ~ (v1_xboole_0 @ X0)
% 30.49/30.70           | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.70           | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('sup-', [status(thm)], ['142', '226'])).
% 30.49/30.70  thf('228', plain,
% 30.49/30.70      ((![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C_1)) | ~ (v1_xboole_0 @ X0)))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('simplify', [status(thm)], ['227'])).
% 30.49/30.70  thf('229', plain,
% 30.49/30.70      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 30.49/30.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.70      inference('clc', [status(thm)], ['139', '228'])).
% 30.49/30.70  thf('230', plain,
% 30.49/30.70      (![X23 : $i]:
% 30.49/30.70         (~ (v2_funct_1 @ X23)
% 30.49/30.70          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.70          | ~ (v1_funct_1 @ X23)
% 30.49/30.70          | ~ (v1_relat_1 @ X23))),
% 30.49/30.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.70  thf('231', plain,
% 30.49/30.70      (![X22 : $i]:
% 30.49/30.70         ((v1_funct_1 @ (k2_funct_1 @ X22))
% 30.49/30.70          | ~ (v1_funct_1 @ X22)
% 30.49/30.70          | ~ (v1_relat_1 @ X22))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.70  thf('232', plain,
% 30.49/30.70      (![X22 : $i]:
% 30.49/30.70         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.70          | ~ (v1_funct_1 @ X22)
% 30.49/30.70          | ~ (v1_relat_1 @ X22))),
% 30.49/30.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.70  thf('233', plain,
% 30.49/30.70      (![X23 : $i]:
% 30.49/30.70         (~ (v2_funct_1 @ X23)
% 30.49/30.70          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.70          | ~ (v1_funct_1 @ X23)
% 30.49/30.70          | ~ (v1_relat_1 @ X23))),
% 30.49/30.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.70  thf('234', plain,
% 30.49/30.70      (![X41 : $i]:
% 30.49/30.70         ((v1_funct_2 @ X41 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41))
% 30.49/30.70          | ~ (v1_funct_1 @ X41)
% 30.49/30.70          | ~ (v1_relat_1 @ X41))),
% 30.49/30.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 30.49/30.70  thf('235', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 30.49/30.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 30.49/30.70          | ~ (v1_relat_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v2_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 30.49/30.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 30.49/30.70      inference('sup+', [status(thm)], ['233', '234'])).
% 30.49/30.70  thf('236', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_relat_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 30.49/30.70          | ~ (v2_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_relat_1 @ X0)
% 30.49/30.70          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 30.49/30.70             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 30.49/30.70      inference('sup-', [status(thm)], ['232', '235'])).
% 30.49/30.70  thf('237', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 30.49/30.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 30.49/30.70          | ~ (v2_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_relat_1 @ X0))),
% 30.49/30.70      inference('simplify', [status(thm)], ['236'])).
% 30.49/30.70  thf('238', plain,
% 30.49/30.70      (![X0 : $i]:
% 30.49/30.70         (~ (v1_relat_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v1_relat_1 @ X0)
% 30.49/30.70          | ~ (v1_funct_1 @ X0)
% 30.49/30.70          | ~ (v2_funct_1 @ X0)
% 30.49/30.70          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 30.49/30.71             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['231', '237'])).
% 30.49/30.71  thf('239', plain,
% 30.49/30.71      (![X0 : $i]:
% 30.49/30.71         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 30.49/30.71           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 30.49/30.71          | ~ (v2_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_relat_1 @ X0))),
% 30.49/30.71      inference('simplify', [status(thm)], ['238'])).
% 30.49/30.71  thf('240', plain,
% 30.49/30.71      (![X0 : $i]:
% 30.49/30.71         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 30.49/30.71           (k1_relat_1 @ X0))
% 30.49/30.71          | ~ (v1_relat_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v2_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_relat_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v2_funct_1 @ X0))),
% 30.49/30.71      inference('sup+', [status(thm)], ['230', '239'])).
% 30.49/30.71  thf('241', plain,
% 30.49/30.71      (![X0 : $i]:
% 30.49/30.71         (~ (v2_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_relat_1 @ X0)
% 30.49/30.71          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 30.49/30.71             (k1_relat_1 @ X0)))),
% 30.49/30.71      inference('simplify', [status(thm)], ['240'])).
% 30.49/30.71  thf('242', plain,
% 30.49/30.71      ((((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 30.49/30.71         | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71         | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71         | ~ (v2_funct_1 @ sk_C_1)))
% 30.49/30.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.71      inference('sup+', [status(thm)], ['229', '241'])).
% 30.49/30.71  thf('243', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.71      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.71  thf('244', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('245', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('246', plain, ((v2_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('247', plain,
% 30.49/30.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 30.49/30.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 30.49/30.71      inference('demod', [status(thm)], ['242', '243', '244', '245', '246'])).
% 30.49/30.71  thf('248', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 30.49/30.71      inference('demod', [status(thm)], ['11', '247'])).
% 30.49/30.71  thf('249', plain,
% 30.49/30.71      (~
% 30.49/30.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 30.49/30.71       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 30.49/30.71       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.71      inference('split', [status(esa)], ['0'])).
% 30.49/30.71  thf('250', plain,
% 30.49/30.71      (~
% 30.49/30.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 30.49/30.71      inference('sat_resolution*', [status(thm)], ['10', '248', '249'])).
% 30.49/30.71  thf('251', plain,
% 30.49/30.71      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.49/30.71      inference('simpl_trail', [status(thm)], ['1', '250'])).
% 30.49/30.71  thf('252', plain,
% 30.49/30.71      (![X23 : $i]:
% 30.49/30.71         (~ (v2_funct_1 @ X23)
% 30.49/30.71          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.71          | ~ (v1_funct_1 @ X23)
% 30.49/30.71          | ~ (v1_relat_1 @ X23))),
% 30.49/30.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.71  thf('253', plain,
% 30.49/30.71      (![X22 : $i]:
% 30.49/30.71         ((v1_funct_1 @ (k2_funct_1 @ X22))
% 30.49/30.71          | ~ (v1_funct_1 @ X22)
% 30.49/30.71          | ~ (v1_relat_1 @ X22))),
% 30.49/30.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.71  thf('254', plain,
% 30.49/30.71      (![X22 : $i]:
% 30.49/30.71         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.71          | ~ (v1_funct_1 @ X22)
% 30.49/30.71          | ~ (v1_relat_1 @ X22))),
% 30.49/30.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.71  thf('255', plain,
% 30.49/30.71      (![X23 : $i]:
% 30.49/30.71         (~ (v2_funct_1 @ X23)
% 30.49/30.71          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.71          | ~ (v1_funct_1 @ X23)
% 30.49/30.71          | ~ (v1_relat_1 @ X23))),
% 30.49/30.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.71  thf('256', plain,
% 30.49/30.71      (![X22 : $i]:
% 30.49/30.71         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.71          | ~ (v1_funct_1 @ X22)
% 30.49/30.71          | ~ (v1_relat_1 @ X22))),
% 30.49/30.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.71  thf('257', plain,
% 30.49/30.71      (![X20 : $i]:
% 30.49/30.71         (((k10_relat_1 @ X20 @ (k2_relat_1 @ X20)) = (k1_relat_1 @ X20))
% 30.49/30.71          | ~ (v1_relat_1 @ X20))),
% 30.49/30.71      inference('cnf', [status(esa)], [t169_relat_1])).
% 30.49/30.71  thf('258', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.71      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.71  thf('259', plain,
% 30.49/30.71      (![X22 : $i]:
% 30.49/30.71         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.71          | ~ (v1_funct_1 @ X22)
% 30.49/30.71          | ~ (v1_relat_1 @ X22))),
% 30.49/30.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.71  thf('260', plain,
% 30.49/30.71      (![X23 : $i]:
% 30.49/30.71         (~ (v2_funct_1 @ X23)
% 30.49/30.71          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.71          | ~ (v1_funct_1 @ X23)
% 30.49/30.71          | ~ (v1_relat_1 @ X23))),
% 30.49/30.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.71  thf('261', plain,
% 30.49/30.71      (![X18 : $i, X19 : $i]:
% 30.49/30.71         ((r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k1_relat_1 @ X18))
% 30.49/30.71          | ~ (v1_relat_1 @ X18))),
% 30.49/30.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 30.49/30.71  thf('262', plain,
% 30.49/30.71      (![X0 : $i, X1 : $i]:
% 30.49/30.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 30.49/30.71           (k2_relat_1 @ X0))
% 30.49/30.71          | ~ (v1_relat_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v2_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 30.49/30.71      inference('sup+', [status(thm)], ['260', '261'])).
% 30.49/30.71  thf('263', plain,
% 30.49/30.71      (![X0 : $i, X1 : $i]:
% 30.49/30.71         (~ (v1_relat_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v2_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_relat_1 @ X0)
% 30.49/30.71          | (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 30.49/30.71             (k2_relat_1 @ X0)))),
% 30.49/30.71      inference('sup-', [status(thm)], ['259', '262'])).
% 30.49/30.71  thf('264', plain,
% 30.49/30.71      (![X0 : $i, X1 : $i]:
% 30.49/30.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ X0) @ X1) @ 
% 30.49/30.71           (k2_relat_1 @ X0))
% 30.49/30.71          | ~ (v2_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_funct_1 @ X0)
% 30.49/30.71          | ~ (v1_relat_1 @ X0))),
% 30.49/30.71      inference('simplify', [status(thm)], ['263'])).
% 30.49/30.71  thf('265', plain,
% 30.49/30.71      (![X0 : $i]:
% 30.49/30.71         ((r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0) @ sk_B)
% 30.49/30.71          | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71          | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71          | ~ (v2_funct_1 @ sk_C_1))),
% 30.49/30.71      inference('sup+', [status(thm)], ['258', '264'])).
% 30.49/30.71  thf('266', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('267', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('268', plain, ((v2_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('269', plain,
% 30.49/30.71      (![X0 : $i]:
% 30.49/30.71         (r1_tarski @ (k10_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0) @ sk_B)),
% 30.49/30.71      inference('demod', [status(thm)], ['265', '266', '267', '268'])).
% 30.49/30.71  thf('270', plain,
% 30.49/30.71      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B)
% 30.49/30.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.71      inference('sup+', [status(thm)], ['257', '269'])).
% 30.49/30.71  thf('271', plain,
% 30.49/30.71      ((~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B))),
% 30.49/30.71      inference('sup-', [status(thm)], ['256', '270'])).
% 30.49/30.71  thf('272', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('273', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('274', plain,
% 30.49/30.71      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ sk_B)),
% 30.49/30.71      inference('demod', [status(thm)], ['271', '272', '273'])).
% 30.49/30.71  thf('275', plain,
% 30.49/30.71      (![X4 : $i, X6 : $i]:
% 30.49/30.71         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 30.49/30.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.49/30.71  thf('276', plain,
% 30.49/30.71      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 30.49/30.71        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['274', '275'])).
% 30.49/30.71  thf('277', plain,
% 30.49/30.71      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 30.49/30.71        | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71        | ~ (v2_funct_1 @ sk_C_1)
% 30.49/30.71        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['255', '276'])).
% 30.49/30.71  thf('278', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.71      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.71  thf('279', plain,
% 30.49/30.71      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 30.49/30.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 30.49/30.71  thf('280', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 30.49/30.71      inference('simplify', [status(thm)], ['279'])).
% 30.49/30.71  thf('281', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('282', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('283', plain, ((v2_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('284', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.71      inference('demod', [status(thm)],
% 30.49/30.71                ['277', '278', '280', '281', '282', '283'])).
% 30.49/30.71  thf('285', plain,
% 30.49/30.71      (![X41 : $i]:
% 30.49/30.71         ((m1_subset_1 @ X41 @ 
% 30.49/30.71           (k1_zfmisc_1 @ 
% 30.49/30.71            (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41))))
% 30.49/30.71          | ~ (v1_funct_1 @ X41)
% 30.49/30.71          | ~ (v1_relat_1 @ X41))),
% 30.49/30.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 30.49/30.71  thf('286', plain,
% 30.49/30.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71         (k1_zfmisc_1 @ 
% 30.49/30.71          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))
% 30.49/30.71        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 30.49/30.71      inference('sup+', [status(thm)], ['284', '285'])).
% 30.49/30.71  thf('287', plain,
% 30.49/30.71      ((~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71           (k1_zfmisc_1 @ 
% 30.49/30.71            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['254', '286'])).
% 30.49/30.71  thf('288', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('289', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('290', plain,
% 30.49/30.71      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71           (k1_zfmisc_1 @ 
% 30.49/30.71            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 30.49/30.71      inference('demod', [status(thm)], ['287', '288', '289'])).
% 30.49/30.71  thf('291', plain,
% 30.49/30.71      ((~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71           (k1_zfmisc_1 @ 
% 30.49/30.71            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['253', '290'])).
% 30.49/30.71  thf('292', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('293', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('294', plain,
% 30.49/30.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71        (k1_zfmisc_1 @ 
% 30.49/30.71         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))))),
% 30.49/30.71      inference('demod', [status(thm)], ['291', '292', '293'])).
% 30.49/30.71  thf('295', plain,
% 30.49/30.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))
% 30.49/30.71        | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71        | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71        | ~ (v2_funct_1 @ sk_C_1))),
% 30.49/30.71      inference('sup+', [status(thm)], ['252', '294'])).
% 30.49/30.71  thf('296', plain,
% 30.49/30.71      (![X22 : $i]:
% 30.49/30.71         ((v1_funct_1 @ (k2_funct_1 @ X22))
% 30.49/30.71          | ~ (v1_funct_1 @ X22)
% 30.49/30.71          | ~ (v1_relat_1 @ X22))),
% 30.49/30.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.71  thf('297', plain,
% 30.49/30.71      (![X22 : $i]:
% 30.49/30.71         ((v1_relat_1 @ (k2_funct_1 @ X22))
% 30.49/30.71          | ~ (v1_funct_1 @ X22)
% 30.49/30.71          | ~ (v1_relat_1 @ X22))),
% 30.49/30.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 30.49/30.71  thf('298', plain,
% 30.49/30.71      (![X23 : $i]:
% 30.49/30.71         (~ (v2_funct_1 @ X23)
% 30.49/30.71          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 30.49/30.71          | ~ (v1_funct_1 @ X23)
% 30.49/30.71          | ~ (v1_relat_1 @ X23))),
% 30.49/30.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 30.49/30.71  thf('299', plain,
% 30.49/30.71      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 30.49/30.71      inference('sup-', [status(thm)], ['40', '51'])).
% 30.49/30.71  thf('300', plain,
% 30.49/30.71      (![X8 : $i, X9 : $i]:
% 30.49/30.71         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 30.49/30.71      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 30.49/30.71  thf('301', plain,
% 30.49/30.71      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 30.49/30.71      inference('simplify', [status(thm)], ['300'])).
% 30.49/30.71  thf('302', plain,
% 30.49/30.71      (![X0 : $i, X1 : $i]:
% 30.49/30.71         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 30.49/30.71      inference('sup+', [status(thm)], ['299', '301'])).
% 30.49/30.71  thf('303', plain,
% 30.49/30.71      (![X41 : $i]:
% 30.49/30.71         ((m1_subset_1 @ X41 @ 
% 30.49/30.71           (k1_zfmisc_1 @ 
% 30.49/30.71            (k2_zfmisc_1 @ (k1_relat_1 @ X41) @ (k2_relat_1 @ X41))))
% 30.49/30.71          | ~ (v1_funct_1 @ X41)
% 30.49/30.71          | ~ (v1_relat_1 @ X41))),
% 30.49/30.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 30.49/30.71  thf('304', plain,
% 30.49/30.71      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 30.49/30.71      inference('sup-', [status(thm)], ['40', '51'])).
% 30.49/30.71  thf('305', plain,
% 30.49/30.71      (![X33 : $i, X34 : $i]:
% 30.49/30.71         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 30.49/30.71  thf('306', plain,
% 30.49/30.71      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 30.49/30.71      inference('simplify', [status(thm)], ['300'])).
% 30.49/30.71  thf('307', plain,
% 30.49/30.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 30.49/30.71         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 30.49/30.71      inference('sup+', [status(thm)], ['305', '306'])).
% 30.49/30.71  thf('308', plain,
% 30.49/30.71      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.71        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 30.49/30.71      inference('sup-', [status(thm)], ['15', '16'])).
% 30.49/30.71  thf('309', plain,
% 30.49/30.71      (![X0 : $i]:
% 30.49/30.71         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 30.49/30.71          | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 30.49/30.71      inference('sup-', [status(thm)], ['307', '308'])).
% 30.49/30.71  thf('310', plain,
% 30.49/30.71      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 30.49/30.71        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.71      inference('demod', [status(thm)], ['21', '24'])).
% 30.49/30.71  thf('311', plain,
% 30.49/30.71      (![X0 : $i]:
% 30.49/30.71         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 30.49/30.71          | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.71      inference('sup-', [status(thm)], ['309', '310'])).
% 30.49/30.71  thf('312', plain,
% 30.49/30.71      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('split', [status(esa)], ['0'])).
% 30.49/30.71  thf('313', plain,
% 30.49/30.71      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ k1_xboole_0))
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['311', '312'])).
% 30.49/30.71  thf('314', plain,
% 30.49/30.71      ((![X0 : $i]:
% 30.49/30.71          (~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ (k1_zfmisc_1 @ X0))
% 30.49/30.71           | ~ (v1_xboole_0 @ X0)
% 30.49/30.71           | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['304', '313'])).
% 30.49/30.71  thf('315', plain,
% 30.49/30.71      (((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_xboole_0 @ 
% 30.49/30.71              (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ 
% 30.49/30.71               (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['303', '314'])).
% 30.49/30.71  thf('316', plain,
% 30.49/30.71      (((~ (v1_xboole_0 @ k1_xboole_0)
% 30.49/30.71         | ~ (v1_xboole_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['302', '315'])).
% 30.49/30.71  thf('317', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 30.49/30.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 30.49/30.71  thf('318', plain,
% 30.49/30.71      (((~ (v1_xboole_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('demod', [status(thm)], ['316', '317'])).
% 30.49/30.71  thf('319', plain,
% 30.49/30.71      (((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71         | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71         | ~ (v2_funct_1 @ sk_C_1)
% 30.49/30.71         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['298', '318'])).
% 30.49/30.71  thf('320', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 30.49/30.71      inference('sup+', [status(thm)], ['30', '31'])).
% 30.49/30.71  thf('321', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('322', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('323', plain, ((v2_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('324', plain,
% 30.49/30.71      (((~ (v1_xboole_0 @ sk_B)
% 30.49/30.71         | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('demod', [status(thm)], ['319', '320', '321', '322', '323'])).
% 30.49/30.71  thf('325', plain,
% 30.49/30.71      (((~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71         | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_xboole_0 @ sk_B)))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['297', '324'])).
% 30.49/30.71  thf('326', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('327', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('328', plain,
% 30.49/30.71      (((((sk_A) = (k1_relat_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ~ (v1_xboole_0 @ sk_B)))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('demod', [status(thm)], ['325', '326', '327'])).
% 30.49/30.71  thf('329', plain,
% 30.49/30.71      (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 30.49/30.71      inference('sup-', [status(thm)], ['18', '25'])).
% 30.49/30.71  thf('330', plain,
% 30.49/30.71      (((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('clc', [status(thm)], ['328', '329'])).
% 30.49/30.71  thf('331', plain,
% 30.49/30.71      (((~ (v1_relat_1 @ sk_C_1)
% 30.49/30.71         | ~ (v1_funct_1 @ sk_C_1)
% 30.49/30.71         | ((sk_A) = (k1_relat_1 @ sk_C_1))))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('sup-', [status(thm)], ['296', '330'])).
% 30.49/30.71  thf('332', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('333', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('334', plain,
% 30.49/30.71      ((((sk_A) = (k1_relat_1 @ sk_C_1)))
% 30.49/30.71         <= (~
% 30.49/30.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 30.49/30.71      inference('demod', [status(thm)], ['331', '332', '333'])).
% 30.49/30.71  thf('335', plain,
% 30.49/30.71      (~
% 30.49/30.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 30.49/30.71      inference('sat_resolution*', [status(thm)], ['10', '248', '249'])).
% 30.49/30.71  thf('336', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 30.49/30.71      inference('simpl_trail', [status(thm)], ['334', '335'])).
% 30.49/30.71  thf('337', plain, ((v1_relat_1 @ sk_C_1)),
% 30.49/30.71      inference('sup-', [status(thm)], ['2', '3'])).
% 30.49/30.71  thf('338', plain, ((v1_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('339', plain, ((v2_funct_1 @ sk_C_1)),
% 30.49/30.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 30.49/30.71  thf('340', plain,
% 30.49/30.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 30.49/30.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 30.49/30.71      inference('demod', [status(thm)], ['295', '336', '337', '338', '339'])).
% 30.49/30.71  thf('341', plain, ($false), inference('demod', [status(thm)], ['251', '340'])).
% 30.49/30.71  
% 30.49/30.71  % SZS output end Refutation
% 30.49/30.71  
% 30.49/30.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AKNofSGF5A

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:41 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 887 expanded)
%              Number of leaves         :   43 ( 292 expanded)
%              Depth                    :   23
%              Number of atoms          : 1002 (9585 expanded)
%              Number of equality atoms :   96 ( 764 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('1',plain,(
    ! [X8: $i] :
      ( r2_hidden @ X8 @ ( k1_tarski @ X8 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    r1_tarski @ sk_C_5 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X41 )
      | ( r1_tarski @ ( k1_relat_1 @ X42 ) @ ( k1_relat_1 @ X41 ) )
      | ~ ( r1_tarski @ X42 @ X41 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_C_5 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_5 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('9',plain,(
    ! [X77: $i,X78: $i,X79: $i] :
      ( ( v1_relat_1 @ X77 )
      | ~ ( m1_subset_1 @ X77 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X78 @ X79 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_5 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('13',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ( ( k7_relat_1 @ X47 @ X48 )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_C_5 )
    | ( ( k7_relat_1 @ sk_C_5 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
      = sk_C_5 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('16',plain,
    ( ( k7_relat_1 @ sk_C_5 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
    = sk_C_5 ),
    inference(demod,[status(thm)],['14','15'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('17',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X37 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) )
        = X37 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_5 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('19',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_5 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_5 ) @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X29: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X43 @ X44 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X43 ) @ X44 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('26',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X15: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X15 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','30'])).

thf(t51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( ( k3_xboole_0 @ X20 @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['33','41'])).

thf('43',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_5 ) @ ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['21','42'])).

thf('44',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X47 ) @ X48 )
      | ( ( k7_relat_1 @ X47 @ X48 )
        = X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C_5 )
    | ( ( k7_relat_1 @ sk_C_5 @ ( k1_tarski @ sk_A ) )
      = sk_C_5 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('47',plain,
    ( ( k7_relat_1 @ sk_C_5 @ ( k1_tarski @ sk_A ) )
    = sk_C_5 ),
    inference(demod,[status(thm)],['45','46'])).

thf(t167_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf('48',plain,(
    ! [X73: $i,X74: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X73 @ ( k1_tarski @ X74 ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ X73 @ X74 ) ) )
      | ~ ( v1_funct_1 @ X73 )
      | ~ ( v1_relat_1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[t167_funct_1])).

thf('49',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C_5 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C_5 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C_5 )
    | ~ ( v1_funct_1 @ sk_C_5 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('51',plain,(
    v1_funct_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_5 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C_5 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf(t39_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t39_zfmisc_1])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_C_5 )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_5 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_5 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_5 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_5 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_C_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('57',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( ( k2_relset_1 @ X81 @ X82 @ X80 )
        = ( k2_relat_1 @ X80 ) )
      | ~ ( m1_subset_1 @ X80 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X82 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('58',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_5 )
    = ( k2_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ( k2_relat_1 @ sk_C_5 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_5 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C_5 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','59'])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('61',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k7_relat_1 @ X45 @ X46 )
        = ( k3_xboole_0 @ X45 @ ( k2_zfmisc_1 @ X46 @ ( k2_relat_1 @ X45 ) ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_C_5 @ X0 )
        = ( k3_xboole_0 @ sk_C_5 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ sk_C_5 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_zfmisc_1 @ X14 @ X15 )
        = k1_xboole_0 )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('64',plain,(
    ! [X14: $i] :
      ( ( k2_zfmisc_1 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('66',plain,(
    v1_relat_1 @ sk_C_5 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_C_5 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','64','65','66'])).

thf('68',plain,(
    k1_xboole_0 = sk_C_5 ),
    inference(demod,[status(thm)],['16','67'])).

thf('69',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','68'])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('70',plain,(
    ! [X87: $i,X88: $i,X89: $i,X90: $i] :
      ( ~ ( r2_hidden @ X87 @ X88 )
      | ( X89 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X90 )
      | ~ ( v1_funct_2 @ X90 @ X88 @ X89 )
      | ~ ( m1_subset_1 @ X90 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X88 @ X89 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X90 @ X87 ) @ ( k2_relset_1 @ X88 @ X89 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ k1_xboole_0 @ X0 ) @ ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ k1_xboole_0 ) )
      | ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('73',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( r2_hidden @ X62 @ ( k1_relat_1 @ X63 ) )
      | ( X64 = k1_xboole_0 )
      | ( X64
       != ( k1_funct_1 @ X63 @ X62 ) )
      | ~ ( v1_funct_1 @ X63 )
      | ~ ( v1_relat_1 @ X63 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('74',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( v1_relat_1 @ X63 )
      | ~ ( v1_funct_1 @ X63 )
      | ( ( k1_funct_1 @ X63 @ X62 )
        = k1_xboole_0 )
      | ( r2_hidden @ X62 @ ( k1_relat_1 @ X63 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['72','74'])).

thf('76',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['28','29'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','40'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    k1_xboole_0 = sk_C_5 ),
    inference(demod,[status(thm)],['16','67'])).

thf('82',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_5 )
    = ( k2_relat_1 @ sk_C_5 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C_5 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['54','59'])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_5 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    k1_xboole_0 = sk_C_5 ),
    inference(demod,[status(thm)],['16','67'])).

thf('88',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_2 @ sk_C_5 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    k1_xboole_0 = sk_C_5 ),
    inference(demod,[status(thm)],['16','67'])).

thf('91',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','83','88','91','92'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','40'])).

thf('97',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    $false ),
    inference('sup-',[status(thm)],['1','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AKNofSGF5A
% 0.16/0.37  % Computer   : n004.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:34:54 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 554 iterations in 0.271s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.75  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.75  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.53/0.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.75  thf(sk_C_5_type, type, sk_C_5: $i).
% 0.53/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(d1_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.53/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.53/0.75  thf('0', plain,
% 0.53/0.75      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.53/0.75         (((X9) != (X8)) | (r2_hidden @ X9 @ X10) | ((X10) != (k1_tarski @ X8)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('1', plain, (![X8 : $i]: (r2_hidden @ X8 @ (k1_tarski @ X8))),
% 0.53/0.75      inference('simplify', [status(thm)], ['0'])).
% 0.53/0.75  thf(t62_funct_2, conjecture,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.53/0.75         ( m1_subset_1 @
% 0.53/0.75           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.53/0.75       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.75         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.53/0.75           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.53/0.75            ( m1_subset_1 @
% 0.53/0.75              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.53/0.75          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.53/0.75            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.53/0.75              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C_5 @ 
% 0.53/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C_5 @ 
% 0.53/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t3_subset, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      (![X21 : $i, X22 : $i]:
% 0.53/0.75         ((r1_tarski @ X21 @ X22) | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      ((r1_tarski @ sk_C_5 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['3', '4'])).
% 0.53/0.75  thf(t25_relat_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( v1_relat_1 @ A ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( v1_relat_1 @ B ) =>
% 0.53/0.75           ( ( r1_tarski @ A @ B ) =>
% 0.53/0.75             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.53/0.75               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.53/0.75  thf('6', plain,
% 0.53/0.75      (![X41 : $i, X42 : $i]:
% 0.53/0.75         (~ (v1_relat_1 @ X41)
% 0.53/0.75          | (r1_tarski @ (k1_relat_1 @ X42) @ (k1_relat_1 @ X41))
% 0.53/0.75          | ~ (r1_tarski @ X42 @ X41)
% 0.53/0.75          | ~ (v1_relat_1 @ X42))),
% 0.53/0.75      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.53/0.75  thf('7', plain,
% 0.53/0.75      ((~ (v1_relat_1 @ sk_C_5)
% 0.53/0.75        | (r1_tarski @ (k1_relat_1 @ sk_C_5) @ 
% 0.53/0.75           (k1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.53/0.75        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C_5 @ 
% 0.53/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(cc1_relset_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.75       ( v1_relat_1 @ C ) ))).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X77 : $i, X78 : $i, X79 : $i]:
% 0.53/0.75         ((v1_relat_1 @ X77)
% 0.53/0.75          | ~ (m1_subset_1 @ X77 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X78 @ X79))))),
% 0.53/0.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.53/0.75  thf('10', plain, ((v1_relat_1 @ sk_C_5)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf(fc6_relat_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.53/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      ((r1_tarski @ (k1_relat_1 @ sk_C_5) @ 
% 0.53/0.75        (k1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.53/0.75  thf(t97_relat_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( v1_relat_1 @ B ) =>
% 0.53/0.75       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.53/0.75         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X47 : $i, X48 : $i]:
% 0.53/0.75         (~ (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 0.53/0.75          | ((k7_relat_1 @ X47 @ X48) = (X47))
% 0.53/0.75          | ~ (v1_relat_1 @ X47))),
% 0.53/0.75      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      ((~ (v1_relat_1 @ sk_C_5)
% 0.53/0.75        | ((k7_relat_1 @ sk_C_5 @ 
% 0.53/0.75            (k1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))
% 0.53/0.75            = (sk_C_5)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['12', '13'])).
% 0.53/0.75  thf('15', plain, ((v1_relat_1 @ sk_C_5)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (((k7_relat_1 @ sk_C_5 @ 
% 0.53/0.75         (k1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))) = (sk_C_5))),
% 0.53/0.75      inference('demod', [status(thm)], ['14', '15'])).
% 0.53/0.75  thf(t195_relat_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.75          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.53/0.75               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (![X37 : $i, X38 : $i]:
% 0.53/0.75         (((X37) = (k1_xboole_0))
% 0.53/0.75          | ((k1_relat_1 @ (k2_zfmisc_1 @ X37 @ X38)) = (X37))
% 0.53/0.75          | ((X38) = (k1_xboole_0)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.53/0.75  thf('18', plain,
% 0.53/0.75      ((r1_tarski @ (k1_relat_1 @ sk_C_5) @ 
% 0.53/0.75        (k1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      (((r1_tarski @ (k1_relat_1 @ sk_C_5) @ (k1_tarski @ sk_A))
% 0.53/0.75        | ((sk_B) = (k1_xboole_0))
% 0.53/0.75        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.53/0.75      inference('sup+', [status(thm)], ['17', '18'])).
% 0.53/0.75  thf('20', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('21', plain,
% 0.53/0.75      (((r1_tarski @ (k1_relat_1 @ sk_C_5) @ (k1_tarski @ sk_A))
% 0.53/0.75        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.53/0.75  thf(t111_relat_1, axiom,
% 0.53/0.75    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.53/0.75  thf('22', plain,
% 0.53/0.75      (![X29 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t111_relat_1])).
% 0.53/0.75  thf(t90_relat_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( v1_relat_1 @ B ) =>
% 0.53/0.75       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.53/0.75         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.53/0.75  thf('23', plain,
% 0.53/0.75      (![X43 : $i, X44 : $i]:
% 0.53/0.75         (((k1_relat_1 @ (k7_relat_1 @ X43 @ X44))
% 0.53/0.75            = (k3_xboole_0 @ (k1_relat_1 @ X43) @ X44))
% 0.53/0.75          | ~ (v1_relat_1 @ X43))),
% 0.53/0.75      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k1_relat_1 @ k1_xboole_0)
% 0.53/0.75            = (k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))
% 0.53/0.75          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['22', '23'])).
% 0.53/0.75  thf(t60_relat_1, axiom,
% 0.53/0.75    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.53/0.75     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.75  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.53/0.75  thf('26', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.53/0.75  thf(t113_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.53/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.53/0.75  thf('27', plain,
% 0.53/0.75      (![X14 : $i, X15 : $i]:
% 0.53/0.75         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.53/0.75          | ((X14) != (k1_xboole_0)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (![X15 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['27'])).
% 0.53/0.75  thf('29', plain,
% 0.53/0.75      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.53/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.75  thf('30', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.53/0.75      inference('sup+', [status(thm)], ['28', '29'])).
% 0.53/0.75  thf('31', plain,
% 0.53/0.75      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['24', '25', '26', '30'])).
% 0.53/0.75  thf(t51_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.53/0.75       ( r2_hidden @ B @ A ) ))).
% 0.53/0.75  thf('32', plain,
% 0.53/0.75      (![X19 : $i, X20 : $i]:
% 0.53/0.75         ((r2_hidden @ X19 @ X20)
% 0.53/0.75          | ((k3_xboole_0 @ X20 @ (k1_tarski @ X19)) != (k1_tarski @ X19)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t51_zfmisc_1])).
% 0.53/0.75  thf('33', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['31', '32'])).
% 0.53/0.75  thf(t2_boole, axiom,
% 0.53/0.75    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.75  thf('34', plain,
% 0.53/0.75      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.75  thf(t4_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.53/0.75            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.53/0.75  thf('35', plain,
% 0.53/0.75      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.53/0.75          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.53/0.75      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.53/0.75  thf('36', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.75  thf('37', plain,
% 0.53/0.75      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.75  thf(d7_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.53/0.75       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      (![X0 : $i, X2 : $i]:
% 0.53/0.75         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.53/0.75  thf('39', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['37', '38'])).
% 0.53/0.75  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.53/0.75      inference('simplify', [status(thm)], ['39'])).
% 0.53/0.75  thf('41', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.53/0.75      inference('demod', [status(thm)], ['36', '40'])).
% 0.53/0.75  thf('42', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['33', '41'])).
% 0.53/0.75  thf('43', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_5) @ (k1_tarski @ sk_A))),
% 0.53/0.75      inference('clc', [status(thm)], ['21', '42'])).
% 0.53/0.75  thf('44', plain,
% 0.53/0.75      (![X47 : $i, X48 : $i]:
% 0.53/0.75         (~ (r1_tarski @ (k1_relat_1 @ X47) @ X48)
% 0.53/0.75          | ((k7_relat_1 @ X47 @ X48) = (X47))
% 0.53/0.75          | ~ (v1_relat_1 @ X47))),
% 0.53/0.75      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.53/0.75  thf('45', plain,
% 0.53/0.75      ((~ (v1_relat_1 @ sk_C_5)
% 0.53/0.75        | ((k7_relat_1 @ sk_C_5 @ (k1_tarski @ sk_A)) = (sk_C_5)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['43', '44'])).
% 0.53/0.75  thf('46', plain, ((v1_relat_1 @ sk_C_5)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('47', plain, (((k7_relat_1 @ sk_C_5 @ (k1_tarski @ sk_A)) = (sk_C_5))),
% 0.53/0.75      inference('demod', [status(thm)], ['45', '46'])).
% 0.53/0.75  thf(t167_funct_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.53/0.75       ( r1_tarski @
% 0.53/0.75         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.53/0.75         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.53/0.75  thf('48', plain,
% 0.53/0.75      (![X73 : $i, X74 : $i]:
% 0.53/0.75         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X73 @ (k1_tarski @ X74))) @ 
% 0.53/0.75           (k1_tarski @ (k1_funct_1 @ X73 @ X74)))
% 0.53/0.75          | ~ (v1_funct_1 @ X73)
% 0.53/0.75          | ~ (v1_relat_1 @ X73))),
% 0.53/0.75      inference('cnf', [status(esa)], [t167_funct_1])).
% 0.53/0.75  thf('49', plain,
% 0.53/0.75      (((r1_tarski @ (k2_relat_1 @ sk_C_5) @ 
% 0.53/0.75         (k1_tarski @ (k1_funct_1 @ sk_C_5 @ sk_A)))
% 0.53/0.75        | ~ (v1_relat_1 @ sk_C_5)
% 0.53/0.75        | ~ (v1_funct_1 @ sk_C_5))),
% 0.53/0.75      inference('sup+', [status(thm)], ['47', '48'])).
% 0.53/0.75  thf('50', plain, ((v1_relat_1 @ sk_C_5)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('51', plain, ((v1_funct_1 @ sk_C_5)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('52', plain,
% 0.53/0.75      ((r1_tarski @ (k2_relat_1 @ sk_C_5) @ 
% 0.53/0.75        (k1_tarski @ (k1_funct_1 @ sk_C_5 @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.53/0.75  thf(t39_zfmisc_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.53/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.53/0.75  thf('53', plain,
% 0.53/0.75      (![X16 : $i, X17 : $i]:
% 0.53/0.75         (((X17) = (k1_tarski @ X16))
% 0.53/0.75          | ((X17) = (k1_xboole_0))
% 0.53/0.75          | ~ (r1_tarski @ X17 @ (k1_tarski @ X16)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t39_zfmisc_1])).
% 0.53/0.75  thf('54', plain,
% 0.53/0.75      ((((k2_relat_1 @ sk_C_5) = (k1_xboole_0))
% 0.53/0.75        | ((k2_relat_1 @ sk_C_5) = (k1_tarski @ (k1_funct_1 @ sk_C_5 @ sk_A))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['52', '53'])).
% 0.53/0.75  thf('55', plain,
% 0.53/0.75      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_5)
% 0.53/0.75         != (k1_tarski @ (k1_funct_1 @ sk_C_5 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('56', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C_5 @ 
% 0.53/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.75  thf('57', plain,
% 0.53/0.75      (![X80 : $i, X81 : $i, X82 : $i]:
% 0.53/0.75         (((k2_relset_1 @ X81 @ X82 @ X80) = (k2_relat_1 @ X80))
% 0.53/0.75          | ~ (m1_subset_1 @ X80 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X82))))),
% 0.53/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.75  thf('58', plain,
% 0.53/0.75      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_5)
% 0.53/0.75         = (k2_relat_1 @ sk_C_5))),
% 0.53/0.75      inference('sup-', [status(thm)], ['56', '57'])).
% 0.53/0.75  thf('59', plain,
% 0.53/0.75      (((k2_relat_1 @ sk_C_5) != (k1_tarski @ (k1_funct_1 @ sk_C_5 @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['55', '58'])).
% 0.53/0.75  thf('60', plain, (((k2_relat_1 @ sk_C_5) = (k1_xboole_0))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['54', '59'])).
% 0.53/0.75  thf(t96_relat_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( v1_relat_1 @ B ) =>
% 0.53/0.75       ( ( k7_relat_1 @ B @ A ) =
% 0.53/0.75         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.53/0.75  thf('61', plain,
% 0.53/0.75      (![X45 : $i, X46 : $i]:
% 0.53/0.75         (((k7_relat_1 @ X45 @ X46)
% 0.53/0.75            = (k3_xboole_0 @ X45 @ (k2_zfmisc_1 @ X46 @ (k2_relat_1 @ X45))))
% 0.53/0.75          | ~ (v1_relat_1 @ X45))),
% 0.53/0.75      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.53/0.75  thf('62', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k7_relat_1 @ sk_C_5 @ X0)
% 0.53/0.75            = (k3_xboole_0 @ sk_C_5 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)))
% 0.53/0.75          | ~ (v1_relat_1 @ sk_C_5))),
% 0.53/0.75      inference('sup+', [status(thm)], ['60', '61'])).
% 0.53/0.75  thf('63', plain,
% 0.53/0.75      (![X14 : $i, X15 : $i]:
% 0.53/0.75         (((k2_zfmisc_1 @ X14 @ X15) = (k1_xboole_0))
% 0.53/0.75          | ((X15) != (k1_xboole_0)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.53/0.75  thf('64', plain,
% 0.53/0.75      (![X14 : $i]: ((k2_zfmisc_1 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['63'])).
% 0.53/0.75  thf('65', plain,
% 0.53/0.75      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.75  thf('66', plain, ((v1_relat_1 @ sk_C_5)),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('67', plain, (![X0 : $i]: ((k7_relat_1 @ sk_C_5 @ X0) = (k1_xboole_0))),
% 0.53/0.75      inference('demod', [status(thm)], ['62', '64', '65', '66'])).
% 0.53/0.75  thf('68', plain, (((k1_xboole_0) = (sk_C_5))),
% 0.53/0.75      inference('demod', [status(thm)], ['16', '67'])).
% 0.53/0.75  thf('69', plain,
% 0.53/0.75      ((m1_subset_1 @ k1_xboole_0 @ 
% 0.53/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.53/0.75      inference('demod', [status(thm)], ['2', '68'])).
% 0.53/0.75  thf(t6_funct_2, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.53/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.75       ( ( r2_hidden @ C @ A ) =>
% 0.53/0.75         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.53/0.75           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.53/0.75  thf('70', plain,
% 0.53/0.75      (![X87 : $i, X88 : $i, X89 : $i, X90 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X87 @ X88)
% 0.53/0.75          | ((X89) = (k1_xboole_0))
% 0.53/0.75          | ~ (v1_funct_1 @ X90)
% 0.53/0.75          | ~ (v1_funct_2 @ X90 @ X88 @ X89)
% 0.53/0.75          | ~ (m1_subset_1 @ X90 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X88 @ X89)))
% 0.53/0.75          | (r2_hidden @ (k1_funct_1 @ X90 @ X87) @ 
% 0.53/0.75             (k2_relset_1 @ X88 @ X89 @ X90)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.53/0.75  thf('71', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ (k1_funct_1 @ k1_xboole_0 @ X0) @ 
% 0.53/0.75           (k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ k1_xboole_0))
% 0.53/0.75          | ~ (v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.53/0.75          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.53/0.75          | ((sk_B) = (k1_xboole_0))
% 0.53/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['69', '70'])).
% 0.53/0.75  thf('72', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.53/0.75  thf(d4_funct_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.75       ( ![B:$i,C:$i]:
% 0.53/0.75         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.53/0.75             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.53/0.75               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.53/0.75           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.53/0.75             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.53/0.75               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.53/0.75  thf('73', plain,
% 0.53/0.75      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.53/0.75         ((r2_hidden @ X62 @ (k1_relat_1 @ X63))
% 0.53/0.75          | ((X64) = (k1_xboole_0))
% 0.53/0.75          | ((X64) != (k1_funct_1 @ X63 @ X62))
% 0.53/0.75          | ~ (v1_funct_1 @ X63)
% 0.53/0.75          | ~ (v1_relat_1 @ X63))),
% 0.53/0.75      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.53/0.75  thf('74', plain,
% 0.53/0.75      (![X62 : $i, X63 : $i]:
% 0.53/0.75         (~ (v1_relat_1 @ X63)
% 0.53/0.75          | ~ (v1_funct_1 @ X63)
% 0.53/0.75          | ((k1_funct_1 @ X63 @ X62) = (k1_xboole_0))
% 0.53/0.75          | (r2_hidden @ X62 @ (k1_relat_1 @ X63)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['73'])).
% 0.53/0.75  thf('75', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.53/0.75          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.53/0.75          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.53/0.75          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.53/0.75      inference('sup+', [status(thm)], ['72', '74'])).
% 0.53/0.75  thf('76', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.53/0.75      inference('sup+', [status(thm)], ['28', '29'])).
% 0.53/0.75  thf('77', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.53/0.75          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.53/0.75          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.53/0.75      inference('demod', [status(thm)], ['75', '76'])).
% 0.53/0.75  thf('78', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.53/0.75      inference('demod', [status(thm)], ['36', '40'])).
% 0.53/0.75  thf('79', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (v1_funct_1 @ k1_xboole_0)
% 0.53/0.75          | ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.53/0.75      inference('clc', [status(thm)], ['77', '78'])).
% 0.53/0.75  thf('80', plain, ((v1_funct_1 @ sk_C_5)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('81', plain, (((k1_xboole_0) = (sk_C_5))),
% 0.53/0.75      inference('demod', [status(thm)], ['16', '67'])).
% 0.53/0.75  thf('82', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.53/0.75      inference('demod', [status(thm)], ['80', '81'])).
% 0.53/0.75  thf('83', plain,
% 0.53/0.75      (![X0 : $i]: ((k1_funct_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.75      inference('demod', [status(thm)], ['79', '82'])).
% 0.53/0.75  thf('84', plain,
% 0.53/0.75      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_5)
% 0.53/0.75         = (k2_relat_1 @ sk_C_5))),
% 0.53/0.75      inference('sup-', [status(thm)], ['56', '57'])).
% 0.53/0.75  thf('85', plain, (((k2_relat_1 @ sk_C_5) = (k1_xboole_0))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['54', '59'])).
% 0.53/0.75  thf('86', plain,
% 0.53/0.75      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_5) = (k1_xboole_0))),
% 0.53/0.75      inference('demod', [status(thm)], ['84', '85'])).
% 0.53/0.75  thf('87', plain, (((k1_xboole_0) = (sk_C_5))),
% 0.53/0.75      inference('demod', [status(thm)], ['16', '67'])).
% 0.53/0.75  thf('88', plain,
% 0.53/0.75      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.75      inference('demod', [status(thm)], ['86', '87'])).
% 0.53/0.75  thf('89', plain, ((v1_funct_2 @ sk_C_5 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('90', plain, (((k1_xboole_0) = (sk_C_5))),
% 0.53/0.75      inference('demod', [status(thm)], ['16', '67'])).
% 0.53/0.75  thf('91', plain, ((v1_funct_2 @ k1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.53/0.75      inference('demod', [status(thm)], ['89', '90'])).
% 0.53/0.75  thf('92', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.53/0.75      inference('demod', [status(thm)], ['80', '81'])).
% 0.53/0.75  thf('93', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.53/0.75          | ((sk_B) = (k1_xboole_0))
% 0.53/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['71', '83', '88', '91', '92'])).
% 0.53/0.75  thf('94', plain, (((sk_B) != (k1_xboole_0))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('95', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.53/0.75          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.53/0.75  thf('96', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.53/0.75      inference('demod', [status(thm)], ['36', '40'])).
% 0.53/0.75  thf('97', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.53/0.75      inference('clc', [status(thm)], ['95', '96'])).
% 0.53/0.75  thf('98', plain, ($false), inference('sup-', [status(thm)], ['1', '97'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4G3IIPvA6Q

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 152 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  634 (1786 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t48_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                <=> ? [E: $i] :
                      ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                      & ( m1_subset_1 @ E @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ! [D: $i] :
                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) )
                  <=> ? [E: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C )
                        & ( m1_subset_1 @ E @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_relset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X19 @ X17 ) @ X19 ) @ X17 )
      | ( X18
       != ( k2_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('7',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ X19 @ X17 ) @ X19 ) @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k2_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_4 @ sk_C_2 ) @ sk_D_4 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('10',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( r2_hidden @ ( sk_D_3 @ sk_D_4 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('14',plain,(
    v4_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['16','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ sk_D_4 @ sk_C_2 ) @ sk_B )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['11','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_3 @ sk_D_4 @ sk_C_2 ) @ sk_D_4 ) @ sk_C_2 )
   <= ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('27',plain,(
    ! [X31: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 )
      | ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_3 @ sk_D_4 @ sk_C_2 ) @ sk_B )
   <= ( ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) )
      & ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
    | ~ ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('33',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_E @ sk_B )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) )
   <= ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('38',plain,
    ( ~ ( m1_subset_1 @ sk_E @ sk_B )
   <= ( ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) )
      & ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 )
    | ~ ! [X31: $i] :
          ( ~ ( m1_subset_1 @ X31 @ sk_B )
          | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
    | ! [X31: $i] :
        ( ~ ( m1_subset_1 @ X31 @ sk_B )
        | ~ ( r2_hidden @ ( k4_tarski @ X31 @ sk_D_4 ) @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('42',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 )
      | ( r2_hidden @ X16 @ X18 )
      | ( X18
       != ( k2_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('44',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X16 @ ( k2_relat_1 @ X17 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_D_4 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_D_4 @ ( k2_relat_1 @ sk_C_2 ) )
   <= ~ ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_E @ sk_D_4 ) @ sk_C_2 )
    | ( r2_hidden @ sk_D_4 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['30','39','40','41','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4G3IIPvA6Q
% 0.15/0.34  % Computer   : n002.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:52:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 83 iterations in 0.051s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_D_4_type, type, sk_D_4: $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.51  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 0.22/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(t48_relset_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.22/0.51                   ( ?[E:$i]:
% 0.22/0.51                     ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.22/0.51                       ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.51                  ( ![D:$i]:
% 0.22/0.51                    ( ( r2_hidden @ D @ ( k2_relset_1 @ B @ A @ C ) ) <=>
% 0.22/0.51                      ( ?[E:$i]:
% 0.22/0.51                        ( ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) & 
% 0.22/0.51                          ( m1_subset_1 @ E @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t48_relset_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.51         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.22/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.22/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)
% 0.22/0.51        | (r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))
% 0.22/0.51         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((r2_hidden @ sk_D_4 @ (k2_relat_1 @ sk_C_2)))
% 0.22/0.51         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('sup+', [status(thm)], ['2', '4'])).
% 0.22/0.51  thf(d5_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X19 @ X18)
% 0.22/0.51          | (r2_hidden @ (k4_tarski @ (sk_D_3 @ X19 @ X17) @ X19) @ X17)
% 0.22/0.51          | ((X18) != (k2_relat_1 @ X17)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X17 : $i, X19 : $i]:
% 0.22/0.51         ((r2_hidden @ (k4_tarski @ (sk_D_3 @ X19 @ X17) @ X19) @ X17)
% 0.22/0.51          | ~ (r2_hidden @ X19 @ (k2_relat_1 @ X17)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_D_4 @ sk_C_2) @ sk_D_4) @ sk_C_2))
% 0.22/0.51         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.51  thf(d4_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.22/0.51       ( ![C:$i]:
% 0.22/0.51         ( ( r2_hidden @ C @ B ) <=>
% 0.22/0.51           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 0.22/0.51          | (r2_hidden @ X8 @ X11)
% 0.22/0.51          | ((X11) != (k1_relat_1 @ X10)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         ((r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.22/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (((r2_hidden @ (sk_D_3 @ sk_D_4 @ sk_C_2) @ (k1_relat_1 @ sk_C_2)))
% 0.22/0.51         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc2_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.51         ((v4_relat_1 @ X25 @ X26)
% 0.22/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.51  thf('14', plain, ((v4_relat_1 @ sk_C_2 @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf(d18_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X6 : $i, X7 : $i]:
% 0.22/0.51         (~ (v4_relat_1 @ X6 @ X7)
% 0.22/0.51          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.22/0.51          | ~ (v1_relat_1 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(cc1_relset_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.51       ( v1_relat_1 @ C ) ))).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.51         ((v1_relat_1 @ X22)
% 0.22/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.22/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.51  thf('19', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['16', '19'])).
% 0.22/0.51  thf(t3_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.51  thf(t4_subset, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.51          | (m1_subset_1 @ X3 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X0 @ sk_B)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (((m1_subset_1 @ (sk_D_3 @ sk_D_4 @ sk_C_2) @ sk_B))
% 0.22/0.51         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['11', '24'])).
% 0.22/0.51  thf('26', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ (sk_D_3 @ sk_D_4 @ sk_C_2) @ sk_D_4) @ sk_C_2))
% 0.22/0.51         <= (((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X31 : $i]:
% 0.22/0.51         (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2)
% 0.22/0.51          | ~ (r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      ((![X31 : $i]:
% 0.22/0.51          (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2)))
% 0.22/0.51         <= ((![X31 : $i]:
% 0.22/0.51                (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51                 | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2))))),
% 0.22/0.51      inference('split', [status(esa)], ['27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      ((~ (m1_subset_1 @ (sk_D_3 @ sk_D_4 @ sk_C_2) @ sk_B))
% 0.22/0.51         <= ((![X31 : $i]:
% 0.22/0.51                (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51                 | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2))) & 
% 0.22/0.51             ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['26', '28'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))) | 
% 0.22/0.51       ~
% 0.22/0.51       (![X31 : $i]:
% 0.22/0.51          (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['25', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.51         ((r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.22/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_2)))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((m1_subset_1 @ X0 @ sk_B)
% 0.22/0.51          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (((m1_subset_1 @ sk_E @ sk_B))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      ((![X31 : $i]:
% 0.22/0.51          (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2)))
% 0.22/0.51         <= ((![X31 : $i]:
% 0.22/0.51                (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51                 | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2))))),
% 0.22/0.51      inference('split', [status(esa)], ['27'])).
% 0.22/0.51  thf('38', plain,
% 0.22/0.51      ((~ (m1_subset_1 @ sk_E @ sk_B))
% 0.22/0.51         <= ((![X31 : $i]:
% 0.22/0.51                (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51                 | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2))) & 
% 0.22/0.51             ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.51  thf('39', plain,
% 0.22/0.51      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)) | 
% 0.22/0.51       ~
% 0.22/0.51       (![X31 : $i]:
% 0.22/0.51          (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '38'])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))) | 
% 0.22/0.51       (![X31 : $i]:
% 0.22/0.51          (~ (m1_subset_1 @ X31 @ sk_B)
% 0.22/0.51           | ~ (r2_hidden @ (k4_tarski @ X31 @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['27'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)) | 
% 0.22/0.51       ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('42', plain,
% 0.22/0.51      (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['3'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.51         (~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17)
% 0.22/0.51          | (r2_hidden @ X16 @ X18)
% 0.22/0.51          | ((X18) != (k2_relat_1 @ X17)))),
% 0.22/0.51      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.22/0.51  thf('44', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.51         ((r2_hidden @ X16 @ (k2_relat_1 @ X17))
% 0.22/0.51          | ~ (r2_hidden @ (k4_tarski @ X15 @ X16) @ X17))),
% 0.22/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (((r2_hidden @ sk_D_4 @ (k2_relat_1 @ sk_C_2)))
% 0.22/0.51         <= (((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['42', '44'])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.51  thf('47', plain,
% 0.22/0.51      ((~ (r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('split', [status(esa)], ['27'])).
% 0.22/0.51  thf('48', plain,
% 0.22/0.51      ((~ (r2_hidden @ sk_D_4 @ (k2_relat_1 @ sk_C_2)))
% 0.22/0.51         <= (~ ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2))))),
% 0.22/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (~ ((r2_hidden @ (k4_tarski @ sk_E @ sk_D_4) @ sk_C_2)) | 
% 0.22/0.51       ((r2_hidden @ sk_D_4 @ (k2_relset_1 @ sk_B @ sk_A @ sk_C_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['45', '48'])).
% 0.22/0.51  thf('50', plain, ($false),
% 0.22/0.51      inference('sat_resolution*', [status(thm)],
% 0.22/0.51                ['30', '39', '40', '41', '49'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.37/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0w4Uy5nT2V

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:56 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 886 expanded)
%              Number of leaves         :   31 ( 257 expanded)
%              Depth                    :   32
%              Number of atoms          : 2153 (16819 expanded)
%              Number of equality atoms :  130 ( 850 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(t5_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( ( k1_relat_1 @ C )
              = A )
            & ! [D: $i] :
                ( ( r2_hidden @ D @ A )
               => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t5_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) )
                & ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ X13 )
      | ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( X13
        = ( k10_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_A @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_A @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_A
        = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ! [X30: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X30 ) @ sk_B )
      | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ X0 @ sk_C_1 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ X13 )
      | ~ ( r2_hidden @ ( sk_D_1 @ X13 @ X14 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X15 @ ( sk_D_1 @ X13 @ X14 @ X15 ) ) @ X14 )
      | ( X13
        = ( k10_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( k1_relat_1 @ X0 ) @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ X0 @ sk_C_1 ) ) @ X0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = ( k10_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_1 @ sk_A @ X0 @ sk_C_1 ) ) @ X0 )
      | ( sk_A
        = ( k10_relat_1 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( sk_A
      = ( k10_relat_1 @ sk_C_1 @ sk_B ) )
    | ( sk_A
      = ( k10_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','28'])).

thf('30',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X26 @ ( k10_relat_1 @ X26 @ X27 ) ) @ X27 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf('32',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( ( sk_C @ X19 @ X20 )
        = ( k1_funct_1 @ X20 @ ( sk_D_2 @ X19 @ X20 ) ) )
      | ( X19
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( r2_hidden @ ( sk_D_2 @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( X19
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ sk_C_1 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X0 @ sk_C_1 ) @ sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( X24
       != ( k1_funct_1 @ X20 @ X25 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('45',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( X23
        = ( k1_funct_1 @ X20 @ ( sk_D_3 @ X23 @ X20 ) ) )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('57',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X20 ) )
      | ( X23
        = ( k1_funct_1 @ X20 @ ( sk_D_3 @ X23 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( ( sk_C @ X0 @ sk_C_1 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_3 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( ( sk_C @ X0 @ sk_C_1 )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_3 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( ( sk_C @ X19 @ X20 )
        = ( k1_funct_1 @ X20 @ ( sk_D_2 @ X19 @ X20 ) ) )
      | ( X19
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('64',plain,(
    ! [X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X20 ) )
      | ( X23
        = ( k1_funct_1 @ X20 @ ( sk_D_3 @ X23 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_3 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) ) @ sk_C_1 ) ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_3 @ ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_3 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['62','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_3 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_D_3 @ ( sk_C @ X0 @ sk_C_1 ) @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) )
        = ( sk_C @ X0 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( ( k1_funct_1 @ sk_C_1 @ ( sk_D_2 @ X0 @ sk_C_1 ) )
        = ( sk_C @ X0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( r2_hidden @ ( sk_D_2 @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( X19
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('77',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( r2_hidden @ ( sk_D_2 @ X19 @ X20 ) @ ( k1_relat_1 @ X20 ) )
      | ( X19
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('78',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X1 @ X3 )
      | ( X2
       != ( k1_funct_1 @ X4 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('79',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X1 @ X3 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X4 ) )
      | ( zip_tseitin_0 @ X1 @ ( k1_funct_1 @ X4 @ X1 ) @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X1 @ X0 ) ) @ X2 @ X0 )
      | ~ ( r2_hidden @ ( sk_D_2 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_C_1 ) @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_C_1 ) @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_C_1 ) @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('89',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['88','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k9_relat_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ ( k9_relat_1 @ sk_C_1 @ sk_A ) )
    | ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(eq_fact,[status(thm)],['94'])).

thf('96',plain,(
    ! [X6: $i,X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('97',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X10 @ X6 @ X7 ) @ X10 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 )
      = ( k1_funct_1 @ sk_C_1 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( ( sk_C @ X19 @ X20 )
        = ( k1_funct_1 @ X20 @ ( sk_D_2 @ X19 @ X20 ) ) )
      | ( X19
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_D_2 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X6: $i,X7: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X6 @ X7 )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X7 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['110'])).

thf('112',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( ( sk_C @ X19 @ X20 )
       != ( k1_funct_1 @ X20 @ X21 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X20 ) )
      | ( X19
        = ( k2_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( sk_C @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 )
       != ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) @ X0 )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( ( sk_C @ ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_C_1 )
     != ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) )
    | ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 )
     != ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) )
    | ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120'])).

thf('122',plain,
    ( ~ ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) @ sk_A )
    | ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( zip_tseitin_0 @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('125',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_E_1 @ ( sk_C @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ sk_C_1 ) @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k9_relat_1 @ sk_C_1 @ sk_A )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['122','125'])).

thf('127',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['35','126'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( v1_funct_2 @ X28 @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('129',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('135',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('137',plain,(
    ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['4','135','136'])).

thf('138',plain,(
    ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','137'])).

thf('139',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['35','126'])).

thf('140',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X29 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X28 ) @ X29 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('141',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['138','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0w4Uy5nT2V
% 0.14/0.38  % Computer   : n020.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 18:24:52 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 2.72/2.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.72/2.93  % Solved by: fo/fo7.sh
% 2.72/2.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.93  % done 950 iterations in 2.448s
% 2.72/2.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.72/2.93  % SZS output start Refutation
% 2.72/2.93  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 2.72/2.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.72/2.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.72/2.93  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.93  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 2.72/2.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.72/2.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.72/2.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.72/2.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.72/2.93  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.72/2.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.72/2.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.72/2.93  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.72/2.93  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i).
% 2.72/2.93  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.72/2.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.72/2.93  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.72/2.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.72/2.93  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 2.72/2.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.72/2.93  thf(sk_B_type, type, sk_B: $i).
% 2.72/2.93  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 2.72/2.93  thf(t5_funct_2, conjecture,
% 2.72/2.93    (![A:$i,B:$i,C:$i]:
% 2.72/2.93     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.72/2.93       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 2.72/2.93           ( ![D:$i]:
% 2.72/2.93             ( ( r2_hidden @ D @ A ) =>
% 2.72/2.93               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 2.72/2.93         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.93           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 2.72/2.93  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.93    (~( ![A:$i,B:$i,C:$i]:
% 2.72/2.93        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.72/2.93          ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 2.72/2.93              ( ![D:$i]:
% 2.72/2.93                ( ( r2_hidden @ D @ A ) =>
% 2.72/2.93                  ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) ) =>
% 2.72/2.93            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.93              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 2.72/2.93    inference('cnf.neg', [status(esa)], [t5_funct_2])).
% 2.72/2.93  thf('0', plain,
% 2.72/2.93      ((~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 2.72/2.93        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('1', plain,
% 2.72/2.93      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 2.72/2.93         <= (~
% 2.72/2.93             ((m1_subset_1 @ sk_C_1 @ 
% 2.72/2.93               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 2.72/2.93      inference('split', [status(esa)], ['0'])).
% 2.72/2.93  thf('2', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('3', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 2.72/2.93      inference('split', [status(esa)], ['0'])).
% 2.72/2.93  thf('4', plain, (((v1_funct_1 @ sk_C_1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['2', '3'])).
% 2.72/2.93  thf('5', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf(d13_funct_1, axiom,
% 2.72/2.93    (![A:$i]:
% 2.72/2.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.93       ( ![B:$i,C:$i]:
% 2.72/2.93         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 2.72/2.93           ( ![D:$i]:
% 2.72/2.93             ( ( r2_hidden @ D @ C ) <=>
% 2.72/2.93               ( ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) & 
% 2.72/2.93                 ( r2_hidden @ ( k1_funct_1 @ A @ D ) @ B ) ) ) ) ) ) ))).
% 2.72/2.93  thf('6', plain,
% 2.72/2.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_D_1 @ X13 @ X14 @ X15) @ X13)
% 2.72/2.93          | (r2_hidden @ (sk_D_1 @ X13 @ X14 @ X15) @ (k1_relat_1 @ X15))
% 2.72/2.93          | ((X13) = (k10_relat_1 @ X15 @ X14))
% 2.72/2.93          | ~ (v1_funct_1 @ X15)
% 2.72/2.93          | ~ (v1_relat_1 @ X15))),
% 2.72/2.93      inference('cnf', [status(esa)], [d13_funct_1])).
% 2.72/2.93  thf('7', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 2.72/2.93          | (r2_hidden @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 2.72/2.93             (k1_relat_1 @ X0)))),
% 2.72/2.93      inference('eq_fact', [status(thm)], ['6'])).
% 2.72/2.93  thf('8', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_D_1 @ sk_A @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 2.72/2.93          | ((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ X0))
% 2.72/2.93          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93          | ~ (v1_relat_1 @ sk_C_1))),
% 2.72/2.93      inference('sup+', [status(thm)], ['5', '7'])).
% 2.72/2.93  thf('9', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('10', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('11', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('12', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('13', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_D_1 @ sk_A @ X0 @ sk_C_1) @ sk_A)
% 2.72/2.93          | ((sk_A) = (k10_relat_1 @ sk_C_1 @ X0)))),
% 2.72/2.93      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 2.72/2.93  thf('14', plain,
% 2.72/2.93      (![X30 : $i]:
% 2.72/2.93         ((r2_hidden @ (k1_funct_1 @ sk_C_1 @ X30) @ sk_B)
% 2.72/2.93          | ~ (r2_hidden @ X30 @ sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('15', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (((sk_A) = (k10_relat_1 @ sk_C_1 @ X0))
% 2.72/2.93          | (r2_hidden @ 
% 2.72/2.93             (k1_funct_1 @ sk_C_1 @ (sk_D_1 @ sk_A @ X0 @ sk_C_1)) @ sk_B))),
% 2.72/2.93      inference('sup-', [status(thm)], ['13', '14'])).
% 2.72/2.93  thf('16', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('17', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 2.72/2.93          | (r2_hidden @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 2.72/2.93             (k1_relat_1 @ X0)))),
% 2.72/2.93      inference('eq_fact', [status(thm)], ['6'])).
% 2.72/2.93  thf('18', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 2.72/2.93          | (r2_hidden @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 2.72/2.93             (k1_relat_1 @ X0)))),
% 2.72/2.93      inference('eq_fact', [status(thm)], ['6'])).
% 2.72/2.93  thf('19', plain,
% 2.72/2.93      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.93         (~ (r2_hidden @ (sk_D_1 @ X13 @ X14 @ X15) @ X13)
% 2.72/2.93          | ~ (r2_hidden @ (sk_D_1 @ X13 @ X14 @ X15) @ (k1_relat_1 @ X15))
% 2.72/2.93          | ~ (r2_hidden @ (k1_funct_1 @ X15 @ (sk_D_1 @ X13 @ X14 @ X15)) @ 
% 2.72/2.93               X14)
% 2.72/2.93          | ((X13) = (k10_relat_1 @ X15 @ X14))
% 2.72/2.93          | ~ (v1_funct_1 @ X15)
% 2.72/2.93          | ~ (v1_relat_1 @ X15))),
% 2.72/2.93      inference('cnf', [status(esa)], [d13_funct_1])).
% 2.72/2.93  thf('20', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 2.72/2.93          | ~ (r2_hidden @ 
% 2.72/2.93               (k1_funct_1 @ X0 @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1)
% 2.72/2.93          | ~ (r2_hidden @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 2.72/2.93               (k1_relat_1 @ X0)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['18', '19'])).
% 2.72/2.93  thf('21', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (r2_hidden @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0) @ 
% 2.72/2.93             (k1_relat_1 @ X0))
% 2.72/2.93          | ~ (r2_hidden @ 
% 2.72/2.93               (k1_funct_1 @ X0 @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1)
% 2.72/2.93          | ~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['20'])).
% 2.72/2.93  thf('22', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ~ (v1_relat_1 @ X0)
% 2.72/2.93          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1))
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (r2_hidden @ 
% 2.72/2.93               (k1_funct_1 @ X0 @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['17', '21'])).
% 2.72/2.93  thf('23', plain,
% 2.72/2.93      (![X0 : $i, X1 : $i]:
% 2.72/2.93         (~ (r2_hidden @ 
% 2.72/2.93             (k1_funct_1 @ X0 @ (sk_D_1 @ (k1_relat_1 @ X0) @ X1 @ X0)) @ X1)
% 2.72/2.93          | ~ (v1_relat_1 @ X0)
% 2.72/2.93          | ~ (v1_funct_1 @ X0)
% 2.72/2.93          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['22'])).
% 2.72/2.93  thf('24', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (~ (r2_hidden @ 
% 2.72/2.93             (k1_funct_1 @ sk_C_1 @ (sk_D_1 @ sk_A @ X0 @ sk_C_1)) @ X0)
% 2.72/2.93          | ((k1_relat_1 @ sk_C_1) = (k10_relat_1 @ sk_C_1 @ X0))
% 2.72/2.93          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93          | ~ (v1_relat_1 @ sk_C_1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['16', '23'])).
% 2.72/2.93  thf('25', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('26', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('28', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (~ (r2_hidden @ 
% 2.72/2.93             (k1_funct_1 @ sk_C_1 @ (sk_D_1 @ sk_A @ X0 @ sk_C_1)) @ X0)
% 2.72/2.93          | ((sk_A) = (k10_relat_1 @ sk_C_1 @ X0)))),
% 2.72/2.93      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 2.72/2.93  thf('29', plain,
% 2.72/2.93      ((((sk_A) = (k10_relat_1 @ sk_C_1 @ sk_B))
% 2.72/2.93        | ((sk_A) = (k10_relat_1 @ sk_C_1 @ sk_B)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['15', '28'])).
% 2.72/2.93  thf('30', plain, (((sk_A) = (k10_relat_1 @ sk_C_1 @ sk_B))),
% 2.72/2.93      inference('simplify', [status(thm)], ['29'])).
% 2.72/2.93  thf(t145_funct_1, axiom,
% 2.72/2.93    (![A:$i,B:$i]:
% 2.72/2.93     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.72/2.93       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 2.72/2.93  thf('31', plain,
% 2.72/2.93      (![X26 : $i, X27 : $i]:
% 2.72/2.93         ((r1_tarski @ (k9_relat_1 @ X26 @ (k10_relat_1 @ X26 @ X27)) @ X27)
% 2.72/2.93          | ~ (v1_funct_1 @ X26)
% 2.72/2.93          | ~ (v1_relat_1 @ X26))),
% 2.72/2.93      inference('cnf', [status(esa)], [t145_funct_1])).
% 2.72/2.93  thf('32', plain,
% 2.72/2.93      (((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_B)
% 2.72/2.93        | ~ (v1_relat_1 @ sk_C_1)
% 2.72/2.93        | ~ (v1_funct_1 @ sk_C_1))),
% 2.72/2.93      inference('sup+', [status(thm)], ['30', '31'])).
% 2.72/2.93  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('35', plain, ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_B)),
% 2.72/2.93      inference('demod', [status(thm)], ['32', '33', '34'])).
% 2.72/2.93  thf(d5_funct_1, axiom,
% 2.72/2.93    (![A:$i]:
% 2.72/2.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.93       ( ![B:$i]:
% 2.72/2.93         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 2.72/2.93           ( ![C:$i]:
% 2.72/2.93             ( ( r2_hidden @ C @ B ) <=>
% 2.72/2.93               ( ?[D:$i]:
% 2.72/2.93                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 2.72/2.93                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 2.72/2.93  thf('36', plain,
% 2.72/2.93      (![X19 : $i, X20 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 2.72/2.93          | ((sk_C @ X19 @ X20) = (k1_funct_1 @ X20 @ (sk_D_2 @ X19 @ X20)))
% 2.72/2.93          | ((X19) = (k2_relat_1 @ X20))
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (v1_relat_1 @ X20))),
% 2.72/2.93      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.93  thf('37', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('38', plain,
% 2.72/2.93      (![X19 : $i, X20 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 2.72/2.93          | (r2_hidden @ (sk_D_2 @ X19 @ X20) @ (k1_relat_1 @ X20))
% 2.72/2.93          | ((X19) = (k2_relat_1 @ X20))
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (v1_relat_1 @ X20))),
% 2.72/2.93      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.93  thf('39', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_D_2 @ X0 @ sk_C_1) @ sk_A)
% 2.72/2.93          | ~ (v1_relat_1 @ sk_C_1)
% 2.72/2.93          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0))),
% 2.72/2.93      inference('sup+', [status(thm)], ['37', '38'])).
% 2.72/2.93  thf('40', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('41', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('42', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_D_2 @ X0 @ sk_C_1) @ sk_A)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0))),
% 2.72/2.93      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.72/2.93  thf('43', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('44', plain,
% 2.72/2.93      (![X20 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 2.72/2.93         (((X22) != (k2_relat_1 @ X20))
% 2.72/2.93          | (r2_hidden @ X24 @ X22)
% 2.72/2.93          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 2.72/2.93          | ((X24) != (k1_funct_1 @ X20 @ X25))
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (v1_relat_1 @ X20))),
% 2.72/2.93      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.93  thf('45', plain,
% 2.72/2.93      (![X20 : $i, X25 : $i]:
% 2.72/2.93         (~ (v1_relat_1 @ X20)
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 2.72/2.93          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['44'])).
% 2.72/2.93  thf('46', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X0 @ sk_A)
% 2.72/2.93          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93          | ~ (v1_relat_1 @ sk_C_1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['43', '45'])).
% 2.72/2.93  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('48', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('49', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (~ (r2_hidden @ X0 @ sk_A)
% 2.72/2.93          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 2.72/2.93      inference('demod', [status(thm)], ['46', '47', '48'])).
% 2.72/2.93  thf('50', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1)) @ 
% 2.72/2.93             (k2_relat_1 @ sk_C_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['42', '49'])).
% 2.72/2.93  thf('51', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | ~ (v1_relat_1 @ sk_C_1)
% 2.72/2.93          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0))),
% 2.72/2.93      inference('sup+', [status(thm)], ['36', '50'])).
% 2.72/2.93  thf('52', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('53', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('54', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0))),
% 2.72/2.93      inference('demod', [status(thm)], ['51', '52', '53'])).
% 2.72/2.93  thf('55', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k2_relat_1 @ sk_C_1)))),
% 2.72/2.93      inference('simplify', [status(thm)], ['54'])).
% 2.72/2.93  thf('56', plain,
% 2.72/2.93      (![X20 : $i, X22 : $i, X23 : $i]:
% 2.72/2.93         (((X22) != (k2_relat_1 @ X20))
% 2.72/2.93          | ((X23) = (k1_funct_1 @ X20 @ (sk_D_3 @ X23 @ X20)))
% 2.72/2.93          | ~ (r2_hidden @ X23 @ X22)
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (v1_relat_1 @ X20))),
% 2.72/2.93      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.93  thf('57', plain,
% 2.72/2.93      (![X20 : $i, X23 : $i]:
% 2.72/2.93         (~ (v1_relat_1 @ X20)
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X20))
% 2.72/2.93          | ((X23) = (k1_funct_1 @ X20 @ (sk_D_3 @ X23 @ X20))))),
% 2.72/2.93      inference('simplify', [status(thm)], ['56'])).
% 2.72/2.93  thf('58', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((sk_C @ X0 @ sk_C_1)
% 2.72/2.93              = (k1_funct_1 @ sk_C_1 @ (sk_D_3 @ (sk_C @ X0 @ sk_C_1) @ sk_C_1)))
% 2.72/2.93          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93          | ~ (v1_relat_1 @ sk_C_1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['55', '57'])).
% 2.72/2.93  thf('59', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('60', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('61', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((sk_C @ X0 @ sk_C_1)
% 2.72/2.93              = (k1_funct_1 @ sk_C_1 @ (sk_D_3 @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))))),
% 2.72/2.93      inference('demod', [status(thm)], ['58', '59', '60'])).
% 2.72/2.93  thf('62', plain,
% 2.72/2.93      (![X19 : $i, X20 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 2.72/2.93          | ((sk_C @ X19 @ X20) = (k1_funct_1 @ X20 @ (sk_D_2 @ X19 @ X20)))
% 2.72/2.93          | ((X19) = (k2_relat_1 @ X20))
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (v1_relat_1 @ X20))),
% 2.72/2.93      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.93  thf('63', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1)) @ 
% 2.72/2.93             (k2_relat_1 @ sk_C_1)))),
% 2.72/2.93      inference('sup-', [status(thm)], ['42', '49'])).
% 2.72/2.93  thf('64', plain,
% 2.72/2.93      (![X20 : $i, X23 : $i]:
% 2.72/2.93         (~ (v1_relat_1 @ X20)
% 2.72/2.93          | ~ (v1_funct_1 @ X20)
% 2.72/2.93          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X20))
% 2.72/2.93          | ((X23) = (k1_funct_1 @ X20 @ (sk_D_3 @ X23 @ X20))))),
% 2.72/2.93      inference('simplify', [status(thm)], ['56'])).
% 2.72/2.93  thf('65', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1))
% 2.72/2.93              = (k1_funct_1 @ sk_C_1 @ 
% 2.72/2.93                 (sk_D_3 @ (k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1)) @ 
% 2.72/2.93                  sk_C_1)))
% 2.72/2.93          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.93          | ~ (v1_relat_1 @ sk_C_1))),
% 2.72/2.93      inference('sup-', [status(thm)], ['63', '64'])).
% 2.72/2.93  thf('66', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('67', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.93  thf('68', plain,
% 2.72/2.93      (![X0 : $i]:
% 2.72/2.93         (((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.93          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.93          | ((k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1))
% 2.72/2.93              = (k1_funct_1 @ sk_C_1 @ 
% 2.72/2.93                 (sk_D_3 @ (k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1)) @ 
% 2.72/2.93                  sk_C_1))))),
% 2.72/2.93      inference('demod', [status(thm)], ['65', '66', '67'])).
% 2.72/2.93  thf('69', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         (((k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1))
% 2.72/2.94            = (k1_funct_1 @ sk_C_1 @ (sk_D_3 @ (sk_C @ X0 @ sk_C_1) @ sk_C_1)))
% 2.72/2.94          | ~ (v1_relat_1 @ sk_C_1)
% 2.72/2.94          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1)))),
% 2.72/2.94      inference('sup+', [status(thm)], ['62', '68'])).
% 2.72/2.94  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('71', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('72', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         (((k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1))
% 2.72/2.94            = (k1_funct_1 @ sk_C_1 @ (sk_D_3 @ (sk_C @ X0 @ sk_C_1) @ sk_C_1)))
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1)))),
% 2.72/2.94      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.72/2.94  thf('73', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | ((k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1))
% 2.72/2.94              = (k1_funct_1 @ sk_C_1 @ (sk_D_3 @ (sk_C @ X0 @ sk_C_1) @ sk_C_1))))),
% 2.72/2.94      inference('simplify', [status(thm)], ['72'])).
% 2.72/2.94  thf('74', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         (((k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1))
% 2.72/2.94            = (sk_C @ X0 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0))),
% 2.72/2.94      inference('sup+', [status(thm)], ['61', '73'])).
% 2.72/2.94  thf('75', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         (((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((k1_funct_1 @ sk_C_1 @ (sk_D_2 @ X0 @ sk_C_1))
% 2.72/2.94              = (sk_C @ X0 @ sk_C_1)))),
% 2.72/2.94      inference('simplify', [status(thm)], ['74'])).
% 2.72/2.94  thf('76', plain,
% 2.72/2.94      (![X19 : $i, X20 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 2.72/2.94          | (r2_hidden @ (sk_D_2 @ X19 @ X20) @ (k1_relat_1 @ X20))
% 2.72/2.94          | ((X19) = (k2_relat_1 @ X20))
% 2.72/2.94          | ~ (v1_funct_1 @ X20)
% 2.72/2.94          | ~ (v1_relat_1 @ X20))),
% 2.72/2.94      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.94  thf('77', plain,
% 2.72/2.94      (![X19 : $i, X20 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 2.72/2.94          | (r2_hidden @ (sk_D_2 @ X19 @ X20) @ (k1_relat_1 @ X20))
% 2.72/2.94          | ((X19) = (k2_relat_1 @ X20))
% 2.72/2.94          | ~ (v1_funct_1 @ X20)
% 2.72/2.94          | ~ (v1_relat_1 @ X20))),
% 2.72/2.94      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.94  thf(d12_funct_1, axiom,
% 2.72/2.94    (![A:$i]:
% 2.72/2.94     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 2.72/2.94       ( ![B:$i,C:$i]:
% 2.72/2.94         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 2.72/2.94           ( ![D:$i]:
% 2.72/2.94             ( ( r2_hidden @ D @ C ) <=>
% 2.72/2.94               ( ?[E:$i]:
% 2.72/2.94                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 2.72/2.94                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 2.72/2.94  thf(zf_stmt_1, axiom,
% 2.72/2.94    (![E:$i,D:$i,B:$i,A:$i]:
% 2.72/2.94     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 2.72/2.94       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 2.72/2.94         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 2.72/2.94  thf('78', plain,
% 2.72/2.94      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.72/2.94         ((zip_tseitin_0 @ X1 @ X2 @ X3 @ X4)
% 2.72/2.94          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X4))
% 2.72/2.94          | ~ (r2_hidden @ X1 @ X3)
% 2.72/2.94          | ((X2) != (k1_funct_1 @ X4 @ X1)))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.72/2.94  thf('79', plain,
% 2.72/2.94      (![X1 : $i, X3 : $i, X4 : $i]:
% 2.72/2.94         (~ (r2_hidden @ X1 @ X3)
% 2.72/2.94          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X4))
% 2.72/2.94          | (zip_tseitin_0 @ X1 @ (k1_funct_1 @ X4 @ X1) @ X3 @ X4))),
% 2.72/2.94      inference('simplify', [status(thm)], ['78'])).
% 2.72/2.94  thf('80', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.94         (~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | (zip_tseitin_0 @ (sk_D_2 @ X1 @ X0) @ 
% 2.72/2.94             (k1_funct_1 @ X0 @ (sk_D_2 @ X1 @ X0)) @ X2 @ X0)
% 2.72/2.94          | ~ (r2_hidden @ (sk_D_2 @ X1 @ X0) @ X2))),
% 2.72/2.94      inference('sup-', [status(thm)], ['77', '79'])).
% 2.72/2.94  thf('81', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         (~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | (zip_tseitin_0 @ (sk_D_2 @ X1 @ X0) @ 
% 2.72/2.94             (k1_funct_1 @ X0 @ (sk_D_2 @ X1 @ X0)) @ (k1_relat_1 @ X0) @ X0)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0))),
% 2.72/2.94      inference('sup-', [status(thm)], ['76', '80'])).
% 2.72/2.94  thf('82', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         ((zip_tseitin_0 @ (sk_D_2 @ X1 @ X0) @ 
% 2.72/2.94           (k1_funct_1 @ X0 @ (sk_D_2 @ X1 @ X0)) @ (k1_relat_1 @ X0) @ X0)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0))),
% 2.72/2.94      inference('simplify', [status(thm)], ['81'])).
% 2.72/2.94  thf('83', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         ((zip_tseitin_0 @ (sk_D_2 @ X0 @ sk_C_1) @ (sk_C @ X0 @ sk_C_1) @ 
% 2.72/2.94           (k1_relat_1 @ sk_C_1) @ sk_C_1)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | ~ (v1_relat_1 @ sk_C_1)
% 2.72/2.94          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0))),
% 2.72/2.94      inference('sup+', [status(thm)], ['75', '82'])).
% 2.72/2.94  thf('84', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('85', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('86', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('87', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         ((zip_tseitin_0 @ (sk_D_2 @ X0 @ sk_C_1) @ (sk_C @ X0 @ sk_C_1) @ 
% 2.72/2.94           sk_A @ sk_C_1)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0))),
% 2.72/2.94      inference('demod', [status(thm)], ['83', '84', '85', '86'])).
% 2.72/2.94  thf('88', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         (((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | (zip_tseitin_0 @ (sk_D_2 @ X0 @ sk_C_1) @ (sk_C @ X0 @ sk_C_1) @ 
% 2.72/2.94             sk_A @ sk_C_1))),
% 2.72/2.94      inference('simplify', [status(thm)], ['87'])).
% 2.72/2.94  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.72/2.94  thf(zf_stmt_3, axiom,
% 2.72/2.94    (![A:$i]:
% 2.72/2.94     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.94       ( ![B:$i,C:$i]:
% 2.72/2.94         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 2.72/2.94           ( ![D:$i]:
% 2.72/2.94             ( ( r2_hidden @ D @ C ) <=>
% 2.72/2.94               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 2.72/2.94  thf('89', plain,
% 2.72/2.94      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 2.72/2.94         (((X9) != (k9_relat_1 @ X7 @ X6))
% 2.72/2.94          | (r2_hidden @ X11 @ X9)
% 2.72/2.94          | ~ (zip_tseitin_0 @ X12 @ X11 @ X6 @ X7)
% 2.72/2.94          | ~ (v1_funct_1 @ X7)
% 2.72/2.94          | ~ (v1_relat_1 @ X7))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.72/2.94  thf('90', plain,
% 2.72/2.94      (![X6 : $i, X7 : $i, X11 : $i, X12 : $i]:
% 2.72/2.94         (~ (v1_relat_1 @ X7)
% 2.72/2.94          | ~ (v1_funct_1 @ X7)
% 2.72/2.94          | ~ (zip_tseitin_0 @ X12 @ X11 @ X6 @ X7)
% 2.72/2.94          | (r2_hidden @ X11 @ (k9_relat_1 @ X7 @ X6)))),
% 2.72/2.94      inference('simplify', [status(thm)], ['89'])).
% 2.72/2.94  thf('91', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k9_relat_1 @ sk_C_1 @ sk_A))
% 2.72/2.94          | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.94          | ~ (v1_relat_1 @ sk_C_1))),
% 2.72/2.94      inference('sup-', [status(thm)], ['88', '90'])).
% 2.72/2.94  thf('92', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('93', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('94', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 2.72/2.94          | ((X0) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k9_relat_1 @ sk_C_1 @ sk_A)))),
% 2.72/2.94      inference('demod', [status(thm)], ['91', '92', '93'])).
% 2.72/2.94  thf('95', plain,
% 2.72/2.94      (((r2_hidden @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ 
% 2.72/2.94         (k9_relat_1 @ sk_C_1 @ sk_A))
% 2.72/2.94        | ((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1)))),
% 2.72/2.94      inference('eq_fact', [status(thm)], ['94'])).
% 2.72/2.94  thf('96', plain,
% 2.72/2.94      (![X6 : $i, X7 : $i, X9 : $i, X10 : $i]:
% 2.72/2.94         (((X9) != (k9_relat_1 @ X7 @ X6))
% 2.72/2.94          | (zip_tseitin_0 @ (sk_E_1 @ X10 @ X6 @ X7) @ X10 @ X6 @ X7)
% 2.72/2.94          | ~ (r2_hidden @ X10 @ X9)
% 2.72/2.94          | ~ (v1_funct_1 @ X7)
% 2.72/2.94          | ~ (v1_relat_1 @ X7))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.72/2.94  thf('97', plain,
% 2.72/2.94      (![X6 : $i, X7 : $i, X10 : $i]:
% 2.72/2.94         (~ (v1_relat_1 @ X7)
% 2.72/2.94          | ~ (v1_funct_1 @ X7)
% 2.72/2.94          | ~ (r2_hidden @ X10 @ (k9_relat_1 @ X7 @ X6))
% 2.72/2.94          | (zip_tseitin_0 @ (sk_E_1 @ X10 @ X6 @ X7) @ X10 @ X6 @ X7))),
% 2.72/2.94      inference('simplify', [status(thm)], ['96'])).
% 2.72/2.94  thf('98', plain,
% 2.72/2.94      ((((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | (zip_tseitin_0 @ 
% 2.72/2.94           (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 2.72/2.94            sk_C_1) @ 
% 2.72/2.94           (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ sk_C_1)
% 2.72/2.94        | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.94        | ~ (v1_relat_1 @ sk_C_1))),
% 2.72/2.94      inference('sup-', [status(thm)], ['95', '97'])).
% 2.72/2.94  thf('99', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('100', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('101', plain,
% 2.72/2.94      ((((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | (zip_tseitin_0 @ 
% 2.72/2.94           (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 2.72/2.94            sk_C_1) @ 
% 2.72/2.94           (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ sk_C_1))),
% 2.72/2.94      inference('demod', [status(thm)], ['98', '99', '100'])).
% 2.72/2.94  thf('102', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.94         (((X2) = (k1_funct_1 @ X0 @ X1))
% 2.72/2.94          | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.72/2.94  thf('103', plain,
% 2.72/2.94      ((((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | ((sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1)
% 2.72/2.94            = (k1_funct_1 @ sk_C_1 @ 
% 2.72/2.94               (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ 
% 2.72/2.94                sk_A @ sk_C_1))))),
% 2.72/2.94      inference('sup-', [status(thm)], ['101', '102'])).
% 2.72/2.94  thf('104', plain,
% 2.72/2.94      (![X19 : $i, X20 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 2.72/2.94          | ((sk_C @ X19 @ X20) = (k1_funct_1 @ X20 @ (sk_D_2 @ X19 @ X20)))
% 2.72/2.94          | ((X19) = (k2_relat_1 @ X20))
% 2.72/2.94          | ~ (v1_funct_1 @ X20)
% 2.72/2.94          | ~ (v1_relat_1 @ X20))),
% 2.72/2.94      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.94  thf('105', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         ((zip_tseitin_0 @ (sk_D_2 @ X1 @ X0) @ 
% 2.72/2.94           (k1_funct_1 @ X0 @ (sk_D_2 @ X1 @ X0)) @ (k1_relat_1 @ X0) @ X0)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0))),
% 2.72/2.94      inference('simplify', [status(thm)], ['81'])).
% 2.72/2.94  thf('106', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         ((zip_tseitin_0 @ (sk_D_2 @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 2.72/2.94           (k1_relat_1 @ X0) @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | ~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 2.72/2.94      inference('sup+', [status(thm)], ['104', '105'])).
% 2.72/2.94  thf('107', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0)
% 2.72/2.94          | (zip_tseitin_0 @ (sk_D_2 @ X1 @ X0) @ (sk_C @ X1 @ X0) @ 
% 2.72/2.94             (k1_relat_1 @ X0) @ X0))),
% 2.72/2.94      inference('simplify', [status(thm)], ['106'])).
% 2.72/2.94  thf('108', plain,
% 2.72/2.94      (![X6 : $i, X7 : $i, X11 : $i, X12 : $i]:
% 2.72/2.94         (~ (v1_relat_1 @ X7)
% 2.72/2.94          | ~ (v1_funct_1 @ X7)
% 2.72/2.94          | ~ (zip_tseitin_0 @ X12 @ X11 @ X6 @ X7)
% 2.72/2.94          | (r2_hidden @ X11 @ (k9_relat_1 @ X7 @ X6)))),
% 2.72/2.94      inference('simplify', [status(thm)], ['89'])).
% 2.72/2.94  thf('109', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         (~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ 
% 2.72/2.94             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0))),
% 2.72/2.94      inference('sup-', [status(thm)], ['107', '108'])).
% 2.72/2.94  thf('110', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 2.72/2.94          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 2.72/2.94          | ((X1) = (k2_relat_1 @ X0))
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0))),
% 2.72/2.94      inference('simplify', [status(thm)], ['109'])).
% 2.72/2.94  thf('111', plain,
% 2.72/2.94      (![X0 : $i]:
% 2.72/2.94         (~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 2.72/2.94          | (r2_hidden @ (sk_C @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0) @ 
% 2.72/2.94             (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 2.72/2.94      inference('eq_fact', [status(thm)], ['110'])).
% 2.72/2.94  thf('112', plain,
% 2.72/2.94      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.72/2.94         (~ (r2_hidden @ (sk_C @ X19 @ X20) @ X19)
% 2.72/2.94          | ((sk_C @ X19 @ X20) != (k1_funct_1 @ X20 @ X21))
% 2.72/2.94          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X20))
% 2.72/2.94          | ((X19) = (k2_relat_1 @ X20))
% 2.72/2.94          | ~ (v1_funct_1 @ X20)
% 2.72/2.94          | ~ (v1_relat_1 @ X20))),
% 2.72/2.94      inference('cnf', [status(esa)], [d5_funct_1])).
% 2.72/2.94  thf('113', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0))
% 2.72/2.94          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.72/2.94          | ((sk_C @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0)
% 2.72/2.94              != (k1_funct_1 @ X0 @ X1)))),
% 2.72/2.94      inference('sup-', [status(thm)], ['111', '112'])).
% 2.72/2.94  thf('114', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i]:
% 2.72/2.94         (((sk_C @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) @ X0)
% 2.72/2.94            != (k1_funct_1 @ X0 @ X1))
% 2.72/2.94          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 2.72/2.94          | ~ (v1_relat_1 @ X0)
% 2.72/2.94          | ~ (v1_funct_1 @ X0)
% 2.72/2.94          | ((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (k2_relat_1 @ X0)))),
% 2.72/2.94      inference('simplify', [status(thm)], ['113'])).
% 2.72/2.94  thf('115', plain,
% 2.72/2.94      ((((sk_C @ (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) @ sk_C_1)
% 2.72/2.94          != (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1))
% 2.72/2.94        | ((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | ((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 2.72/2.94            = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.94        | ~ (v1_relat_1 @ sk_C_1)
% 2.72/2.94        | ~ (r2_hidden @ 
% 2.72/2.94             (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 2.72/2.94              sk_C_1) @ 
% 2.72/2.94             (k1_relat_1 @ sk_C_1)))),
% 2.72/2.94      inference('sup-', [status(thm)], ['103', '114'])).
% 2.72/2.94  thf('116', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('117', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('118', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('119', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('120', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('121', plain,
% 2.72/2.94      ((((sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1)
% 2.72/2.94          != (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1))
% 2.72/2.94        | ((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | ((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | ~ (r2_hidden @ 
% 2.72/2.94             (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 2.72/2.94              sk_C_1) @ 
% 2.72/2.94             sk_A))),
% 2.72/2.94      inference('demod', [status(thm)],
% 2.72/2.94                ['115', '116', '117', '118', '119', '120'])).
% 2.72/2.94  thf('122', plain,
% 2.72/2.94      ((~ (r2_hidden @ 
% 2.72/2.94           (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 2.72/2.94            sk_C_1) @ 
% 2.72/2.94           sk_A)
% 2.72/2.94        | ((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1)))),
% 2.72/2.94      inference('simplify', [status(thm)], ['121'])).
% 2.72/2.94  thf('123', plain,
% 2.72/2.94      ((((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | (zip_tseitin_0 @ 
% 2.72/2.94           (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 2.72/2.94            sk_C_1) @ 
% 2.72/2.94           (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ sk_C_1))),
% 2.72/2.94      inference('demod', [status(thm)], ['98', '99', '100'])).
% 2.72/2.94  thf('124', plain,
% 2.72/2.94      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.72/2.94         ((r2_hidden @ X1 @ X3) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.72/2.94  thf('125', plain,
% 2.72/2.94      ((((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 2.72/2.94        | (r2_hidden @ 
% 2.72/2.94           (sk_E_1 @ (sk_C @ (k9_relat_1 @ sk_C_1 @ sk_A) @ sk_C_1) @ sk_A @ 
% 2.72/2.94            sk_C_1) @ 
% 2.72/2.94           sk_A))),
% 2.72/2.94      inference('sup-', [status(thm)], ['123', '124'])).
% 2.72/2.94  thf('126', plain, (((k9_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))),
% 2.72/2.94      inference('clc', [status(thm)], ['122', '125'])).
% 2.72/2.94  thf('127', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 2.72/2.94      inference('demod', [status(thm)], ['35', '126'])).
% 2.72/2.94  thf(t4_funct_2, axiom,
% 2.72/2.94    (![A:$i,B:$i]:
% 2.72/2.94     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.72/2.94       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.72/2.94         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 2.72/2.94           ( m1_subset_1 @
% 2.72/2.94             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 2.72/2.94  thf('128', plain,
% 2.72/2.94      (![X28 : $i, X29 : $i]:
% 2.72/2.94         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 2.72/2.94          | (v1_funct_2 @ X28 @ (k1_relat_1 @ X28) @ X29)
% 2.72/2.94          | ~ (v1_funct_1 @ X28)
% 2.72/2.94          | ~ (v1_relat_1 @ X28))),
% 2.72/2.94      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.72/2.94  thf('129', plain,
% 2.72/2.94      ((~ (v1_relat_1 @ sk_C_1)
% 2.72/2.94        | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.94        | (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 2.72/2.94      inference('sup-', [status(thm)], ['127', '128'])).
% 2.72/2.94  thf('130', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('131', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('132', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('133', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 2.72/2.94      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 2.72/2.94  thf('134', plain,
% 2.72/2.94      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))
% 2.72/2.94         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 2.72/2.94      inference('split', [status(esa)], ['0'])).
% 2.72/2.94  thf('135', plain, (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 2.72/2.94      inference('sup-', [status(thm)], ['133', '134'])).
% 2.72/2.94  thf('136', plain,
% 2.72/2.94      (~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 2.72/2.94       ~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)) | ~ ((v1_funct_1 @ sk_C_1))),
% 2.72/2.94      inference('split', [status(esa)], ['0'])).
% 2.72/2.94  thf('137', plain,
% 2.72/2.94      (~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 2.72/2.94      inference('sat_resolution*', [status(thm)], ['4', '135', '136'])).
% 2.72/2.94  thf('138', plain,
% 2.72/2.94      (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.94      inference('simpl_trail', [status(thm)], ['1', '137'])).
% 2.72/2.94  thf('139', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 2.72/2.94      inference('demod', [status(thm)], ['35', '126'])).
% 2.72/2.94  thf('140', plain,
% 2.72/2.94      (![X28 : $i, X29 : $i]:
% 2.72/2.94         (~ (r1_tarski @ (k2_relat_1 @ X28) @ X29)
% 2.72/2.94          | (m1_subset_1 @ X28 @ 
% 2.72/2.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X28) @ X29)))
% 2.72/2.94          | ~ (v1_funct_1 @ X28)
% 2.72/2.94          | ~ (v1_relat_1 @ X28))),
% 2.72/2.94      inference('cnf', [status(esa)], [t4_funct_2])).
% 2.72/2.94  thf('141', plain,
% 2.72/2.94      ((~ (v1_relat_1 @ sk_C_1)
% 2.72/2.94        | ~ (v1_funct_1 @ sk_C_1)
% 2.72/2.94        | (m1_subset_1 @ sk_C_1 @ 
% 2.72/2.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))))),
% 2.72/2.94      inference('sup-', [status(thm)], ['139', '140'])).
% 2.72/2.94  thf('142', plain, ((v1_relat_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('143', plain, ((v1_funct_1 @ sk_C_1)),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('144', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 2.72/2.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.94  thf('145', plain,
% 2.72/2.94      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.94      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 2.72/2.94  thf('146', plain, ($false), inference('demod', [status(thm)], ['138', '145'])).
% 2.72/2.94  
% 2.72/2.94  % SZS output end Refutation
% 2.72/2.94  
% 2.72/2.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

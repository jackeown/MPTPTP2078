%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CWOGS6ZIeN

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  68 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  566 (1546 expanded)
%              Number of equality atoms :   42 ( 182 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t80_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( ! [G: $i] :
            ( ( m1_subset_1 @ G @ A )
           => ! [H: $i] :
                ( ( m1_subset_1 @ H @ B )
               => ! [I: $i] :
                    ( ( m1_subset_1 @ I @ C )
                   => ! [J: $i] :
                        ( ( m1_subset_1 @ J @ D )
                       => ( ( F
                            = ( k4_mcart_1 @ G @ H @ I @ J ) )
                         => ( E = H ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ( ! [G: $i] :
              ( ( m1_subset_1 @ G @ A )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ B )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ C )
                     => ! [J: $i] :
                          ( ( m1_subset_1 @ J @ D )
                         => ( ( F
                              = ( k4_mcart_1 @ G @ H @ I @ J ) )
                           => ( E = H ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X48
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) @ ( k9_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) @ ( k10_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) @ ( k11_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47 ) )
      | ( X47 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('2',plain,
    ( ( sk_D_1 = k1_xboole_0 )
    | ( sk_F
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) ) )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_F
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('9',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X40 ) @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('10',plain,(
    m1_subset_1 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X52 @ sk_B )
      | ~ ( m1_subset_1 @ X53 @ sk_D_1 )
      | ( sk_F
       != ( k4_mcart_1 @ X54 @ X52 @ X55 @ X53 ) )
      | ( sk_E = X52 )
      | ~ ( m1_subset_1 @ X55 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X54 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_E
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_F != sk_F )
    | ~ ( m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X26 @ X27 @ X28 @ X29 @ X30 ) @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('18',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('21',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('23',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X31 @ X32 @ X33 @ X34 @ X35 ) @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('24',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_F != sk_F ),
    inference(demod,[status(thm)],['15','18','21','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CWOGS6ZIeN
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:17:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 58 iterations in 0.039s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(t80_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50       ( ( ![G:$i]:
% 0.21/0.50           ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.50             ( ![H:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.50                 ( ![I:$i]:
% 0.21/0.50                   ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.50                     ( ![J:$i]:
% 0.21/0.50                       ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.50                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.50                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.50         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50          ( ( ![G:$i]:
% 0.21/0.50              ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.50                ( ![H:$i]:
% 0.21/0.50                  ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.50                    ( ![I:$i]:
% 0.21/0.50                      ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.50                        ( ![J:$i]:
% 0.21/0.50                          ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.50                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.50                              ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.50            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50              ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t80_mcart_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t60_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ~( ![E:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50                 ( ( E ) =
% 0.21/0.50                   ( k4_mcart_1 @
% 0.21/0.50                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.50                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.50                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.50                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.21/0.50         (((X44) = (k1_xboole_0))
% 0.21/0.50          | ((X45) = (k1_xboole_0))
% 0.21/0.50          | ((X46) = (k1_xboole_0))
% 0.21/0.50          | ((X48)
% 0.21/0.50              = (k4_mcart_1 @ (k8_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48) @ 
% 0.21/0.50                 (k9_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48) @ 
% 0.21/0.50                 (k10_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48) @ 
% 0.21/0.50                 (k11_mcart_1 @ X44 @ X45 @ X46 @ X47 @ X48)))
% 0.21/0.50          | ~ (m1_subset_1 @ X48 @ (k4_zfmisc_1 @ X44 @ X45 @ X46 @ X47))
% 0.21/0.50          | ((X47) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((((sk_D_1) = (k1_xboole_0))
% 0.21/0.50        | ((sk_F)
% 0.21/0.50            = (k4_mcart_1 @ 
% 0.21/0.50               (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50               (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50               (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50               (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F)))
% 0.21/0.50        | ((sk_C_1) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, (((sk_D_1) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (((sk_F)
% 0.21/0.50         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50            (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50            (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50            (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k9_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k9_mcart_1 @ X36 @ X37 @ X38 @ X39 @ X40) @ X37)
% 0.21/0.50          | ~ (m1_subset_1 @ X40 @ (k4_zfmisc_1 @ X36 @ X37 @ X38 @ X39)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k9_mcart_1])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50        sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X52 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X53 @ sk_D_1)
% 0.21/0.50          | ((sk_F) != (k4_mcart_1 @ X54 @ X52 @ X55 @ X53))
% 0.21/0.50          | ((sk_E) = (X52))
% 0.21/0.50          | ~ (m1_subset_1 @ X55 @ sk_C_1)
% 0.21/0.50          | ~ (m1_subset_1 @ X54 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.21/0.50          | ((sk_E) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F))
% 0.21/0.50          | ((sk_F)
% 0.21/0.50              != (k4_mcart_1 @ X0 @ 
% 0.21/0.50                  (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ X1 @ X2))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ sk_D_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (((sk_E) != (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 0.21/0.50          | ((sk_F)
% 0.21/0.50              != (k4_mcart_1 @ X0 @ 
% 0.21/0.50                  (k9_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ X1 @ X2))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ sk_D_1))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((((sk_F) != (sk_F))
% 0.21/0.50        | ~ (m1_subset_1 @ 
% 0.21/0.50             (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ sk_D_1)
% 0.21/0.50        | ~ (m1_subset_1 @ 
% 0.21/0.50             (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ sk_C_1)
% 0.21/0.50        | ~ (m1_subset_1 @ 
% 0.21/0.50             (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k11_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ))).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k11_mcart_1 @ X26 @ X27 @ X28 @ X29 @ X30) @ X29)
% 0.21/0.50          | ~ (m1_subset_1 @ X30 @ (k4_zfmisc_1 @ X26 @ X27 @ X28 @ X29)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k11_mcart_1])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      ((m1_subset_1 @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50        sk_D_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k10_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ))).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k10_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25) @ X23)
% 0.21/0.50          | ~ (m1_subset_1 @ X25 @ (k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k10_mcart_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50        sk_C_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_k8_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50       ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (k8_mcart_1 @ X31 @ X32 @ X33 @ X34 @ X35) @ X31)
% 0.21/0.50          | ~ (m1_subset_1 @ X35 @ (k4_zfmisc_1 @ X31 @ X32 @ X33 @ X34)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_k8_mcart_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      ((m1_subset_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D_1 @ sk_F) @ 
% 0.21/0.50        sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, (((sk_F) != (sk_F))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '18', '21', '24'])).
% 0.21/0.50  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------

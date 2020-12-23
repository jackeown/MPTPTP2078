%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:21 EST 2020

% Result     : Theorem 5.34s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 281 expanded)
%              Number of leaves         :   29 ( 106 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 659 expanded)
%              Number of equality atoms :   70 ( 308 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A != k1_xboole_0
     => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
        & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_3722,plain,(
    ! [D_6727,C_6728,B_6729,A_6730] :
      ( r2_hidden(k1_funct_1(D_6727,C_6728),B_6729)
      | k1_xboole_0 = B_6729
      | ~ r2_hidden(C_6728,A_6730)
      | ~ m1_subset_1(D_6727,k1_zfmisc_1(k2_zfmisc_1(A_6730,B_6729)))
      | ~ v1_funct_2(D_6727,A_6730,B_6729)
      | ~ v1_funct_1(D_6727) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_7444,plain,(
    ! [D_11590,B_11591] :
      ( r2_hidden(k1_funct_1(D_11590,'#skF_5'),B_11591)
      | k1_xboole_0 = B_11591
      | ~ m1_subset_1(D_11590,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_11591)))
      | ~ v1_funct_2(D_11590,'#skF_3',B_11591)
      | ~ v1_funct_1(D_11590) ) ),
    inference(resolution,[status(thm)],[c_46,c_3722])).

tff(c_7453,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_7444])).

tff(c_7460,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_7453])).

tff(c_7462,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7460])).

tff(c_38,plain,(
    ! [B_15,A_14] :
      ( k2_zfmisc_1(k1_tarski(B_15),A_14) != k1_xboole_0
      | k1_xboole_0 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_7474,plain,(
    ! [A_14] :
      ( k2_zfmisc_1(k1_xboole_0,A_14) != k1_xboole_0
      | k1_xboole_0 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7462,c_38])).

tff(c_7528,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7474])).

tff(c_7523,plain,(
    ! [A_14] : k1_xboole_0 = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7474])).

tff(c_7681,plain,(
    ! [A_12732] : A_12732 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_7528,c_7523])).

tff(c_4857,plain,(
    ! [D_7666,B_7667] :
      ( r2_hidden(k1_funct_1(D_7666,'#skF_5'),B_7667)
      | k1_xboole_0 = B_7667
      | ~ m1_subset_1(D_7666,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_7667)))
      | ~ v1_funct_2(D_7666,'#skF_3',B_7667)
      | ~ v1_funct_1(D_7666) ) ),
    inference(resolution,[status(thm)],[c_46,c_3722])).

tff(c_4866,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_48,c_4857])).

tff(c_4873,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_4866])).

tff(c_4875,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4873])).

tff(c_4887,plain,(
    ! [A_14] :
      ( k2_zfmisc_1(k1_xboole_0,A_14) != k1_xboole_0
      | k1_xboole_0 = A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4875,c_38])).

tff(c_4944,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4887])).

tff(c_4936,plain,(
    ! [A_14] : k1_xboole_0 = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4887])).

tff(c_5289,plain,(
    ! [A_9506] : A_9506 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_4944,c_4936])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( '#skF_1'(A_3,B_4,C_5) = B_4
      | '#skF_1'(A_3,B_4,C_5) = A_3
      | '#skF_2'(A_3,B_4,C_5) != B_4
      | k2_tarski(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_195,plain,(
    ! [B_4,C_5] :
      ( '#skF_2'(B_4,B_4,C_5) != B_4
      | k2_tarski(B_4,B_4) = C_5
      | '#skF_1'(B_4,B_4,C_5) = B_4 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_16])).

tff(c_723,plain,(
    ! [B_594] :
      ( '#skF_2'(B_594,B_594,'#skF_5') != B_594
      | k1_tarski(B_594) = '#skF_5'
      | '#skF_1'(B_594,B_594,'#skF_5') = B_594 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_195])).

tff(c_86,plain,(
    ! [D_26,A_27] : r2_hidden(D_26,k2_tarski(A_27,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_89,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_86])).

tff(c_1578,plain,(
    ! [B_1946] :
      ( r2_hidden(B_1946,'#skF_5')
      | '#skF_2'(B_1946,B_1946,'#skF_5') != B_1946
      | '#skF_1'(B_1946,B_1946,'#skF_5') = B_1946 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_89])).

tff(c_40,plain,(
    ! [B_17,A_16] :
      ( ~ r1_tarski(B_17,A_16)
      | ~ r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3804,plain,(
    ! [B_6986] :
      ( ~ r1_tarski('#skF_5',B_6986)
      | '#skF_2'(B_6986,B_6986,'#skF_5') != B_6986
      | '#skF_1'(B_6986,B_6986,'#skF_5') = B_6986 ) ),
    inference(resolution,[status(thm)],[c_1578,c_40])).

tff(c_3808,plain,
    ( '#skF_2'('#skF_5','#skF_5','#skF_5') != '#skF_5'
    | '#skF_1'('#skF_5','#skF_5','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6,c_3804])).

tff(c_3950,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_5') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3808])).

tff(c_5442,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5289,c_3950])).

tff(c_5443,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4873])).

tff(c_163,plain,(
    ! [D_48,B_49,A_50] :
      ( D_48 = B_49
      | D_48 = A_50
      | ~ r2_hidden(D_48,k2_tarski(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_172,plain,(
    ! [D_48,A_9] :
      ( D_48 = A_9
      | D_48 = A_9
      | ~ r2_hidden(D_48,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_163])).

tff(c_5453,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5443,c_172])).

tff(c_5499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_5453])).

tff(c_5501,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3808])).

tff(c_5500,plain,(
    '#skF_1'('#skF_5','#skF_5','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3808])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | '#skF_2'(A_3,B_4,C_5) != B_4
      | k2_tarski(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5514,plain,
    ( ~ r2_hidden('#skF_5','#skF_5')
    | '#skF_2'('#skF_5','#skF_5','#skF_5') != '#skF_5'
    | k2_tarski('#skF_5','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_5500,c_14])).

tff(c_5527,plain,
    ( ~ r2_hidden('#skF_5','#skF_5')
    | '#skF_2'('#skF_5','#skF_5','#skF_5') != '#skF_5'
    | k1_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_5514])).

tff(c_5539,plain,
    ( ~ r2_hidden('#skF_5','#skF_5')
    | k1_tarski('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5501,c_5527])).

tff(c_5540,plain,(
    ~ r2_hidden('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5539])).

tff(c_7780,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7681,c_5540])).

tff(c_7940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_7780])).

tff(c_7941,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7460])).

tff(c_7951,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7941,c_172])).

tff(c_7997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_44,c_7951])).

tff(c_7998,plain,(
    k1_tarski('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5539])).

tff(c_96,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_110,plain,(
    ! [A_9] : ~ r1_tarski(k1_tarski(A_9),A_9) ),
    inference(resolution,[status(thm)],[c_89,c_96])).

tff(c_8013,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7998,c_110])).

tff(c_8058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:30:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.34/2.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.25  
% 5.66/2.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.25  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.66/2.25  
% 5.66/2.25  %Foreground sorts:
% 5.66/2.25  
% 5.66/2.25  
% 5.66/2.25  %Background operators:
% 5.66/2.25  
% 5.66/2.25  
% 5.66/2.25  %Foreground operators:
% 5.66/2.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.66/2.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.66/2.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.66/2.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.66/2.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.66/2.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.66/2.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.66/2.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.66/2.25  tff('#skF_5', type, '#skF_5': $i).
% 5.66/2.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.66/2.25  tff('#skF_6', type, '#skF_6': $i).
% 5.66/2.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.66/2.25  tff('#skF_3', type, '#skF_3': $i).
% 5.66/2.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.66/2.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.66/2.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.66/2.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.66/2.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.66/2.25  tff('#skF_4', type, '#skF_4': $i).
% 5.66/2.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.66/2.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.66/2.25  
% 5.66/2.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.66/2.27  tff(f_87, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 5.66/2.27  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.66/2.27  tff(f_76, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 5.66/2.27  tff(f_59, axiom, (![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 5.66/2.27  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 5.66/2.27  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 5.66/2.27  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.66/2.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.66/2.27  tff(c_44, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.66/2.27  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.66/2.27  tff(c_34, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.66/2.27  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.66/2.27  tff(c_50, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.66/2.27  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.66/2.27  tff(c_3722, plain, (![D_6727, C_6728, B_6729, A_6730]: (r2_hidden(k1_funct_1(D_6727, C_6728), B_6729) | k1_xboole_0=B_6729 | ~r2_hidden(C_6728, A_6730) | ~m1_subset_1(D_6727, k1_zfmisc_1(k2_zfmisc_1(A_6730, B_6729))) | ~v1_funct_2(D_6727, A_6730, B_6729) | ~v1_funct_1(D_6727))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.66/2.27  tff(c_7444, plain, (![D_11590, B_11591]: (r2_hidden(k1_funct_1(D_11590, '#skF_5'), B_11591) | k1_xboole_0=B_11591 | ~m1_subset_1(D_11590, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_11591))) | ~v1_funct_2(D_11590, '#skF_3', B_11591) | ~v1_funct_1(D_11590))), inference(resolution, [status(thm)], [c_46, c_3722])).
% 5.66/2.27  tff(c_7453, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_7444])).
% 5.66/2.27  tff(c_7460, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_7453])).
% 5.66/2.27  tff(c_7462, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7460])).
% 5.66/2.27  tff(c_38, plain, (![B_15, A_14]: (k2_zfmisc_1(k1_tarski(B_15), A_14)!=k1_xboole_0 | k1_xboole_0=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.66/2.27  tff(c_7474, plain, (![A_14]: (k2_zfmisc_1(k1_xboole_0, A_14)!=k1_xboole_0 | k1_xboole_0=A_14)), inference(superposition, [status(thm), theory('equality')], [c_7462, c_38])).
% 5.66/2.27  tff(c_7528, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7474])).
% 5.66/2.27  tff(c_7523, plain, (![A_14]: (k1_xboole_0=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_7474])).
% 5.66/2.27  tff(c_7681, plain, (![A_12732]: (A_12732='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7528, c_7523])).
% 5.66/2.27  tff(c_4857, plain, (![D_7666, B_7667]: (r2_hidden(k1_funct_1(D_7666, '#skF_5'), B_7667) | k1_xboole_0=B_7667 | ~m1_subset_1(D_7666, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_7667))) | ~v1_funct_2(D_7666, '#skF_3', B_7667) | ~v1_funct_1(D_7666))), inference(resolution, [status(thm)], [c_46, c_3722])).
% 5.66/2.27  tff(c_4866, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_48, c_4857])).
% 5.66/2.27  tff(c_4873, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_4866])).
% 5.66/2.27  tff(c_4875, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4873])).
% 5.66/2.27  tff(c_4887, plain, (![A_14]: (k2_zfmisc_1(k1_xboole_0, A_14)!=k1_xboole_0 | k1_xboole_0=A_14)), inference(superposition, [status(thm), theory('equality')], [c_4875, c_38])).
% 5.66/2.27  tff(c_4944, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4887])).
% 5.66/2.27  tff(c_4936, plain, (![A_14]: (k1_xboole_0=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4887])).
% 5.66/2.27  tff(c_5289, plain, (![A_9506]: (A_9506='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4944, c_4936])).
% 5.66/2.27  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.66/2.27  tff(c_16, plain, (![A_3, B_4, C_5]: ('#skF_1'(A_3, B_4, C_5)=B_4 | '#skF_1'(A_3, B_4, C_5)=A_3 | '#skF_2'(A_3, B_4, C_5)!=B_4 | k2_tarski(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.66/2.27  tff(c_195, plain, (![B_4, C_5]: ('#skF_2'(B_4, B_4, C_5)!=B_4 | k2_tarski(B_4, B_4)=C_5 | '#skF_1'(B_4, B_4, C_5)=B_4)), inference(factorization, [status(thm), theory('equality')], [c_16])).
% 5.66/2.27  tff(c_723, plain, (![B_594]: ('#skF_2'(B_594, B_594, '#skF_5')!=B_594 | k1_tarski(B_594)='#skF_5' | '#skF_1'(B_594, B_594, '#skF_5')=B_594)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_195])).
% 5.66/2.27  tff(c_86, plain, (![D_26, A_27]: (r2_hidden(D_26, k2_tarski(A_27, D_26)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.66/2.27  tff(c_89, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_86])).
% 5.66/2.27  tff(c_1578, plain, (![B_1946]: (r2_hidden(B_1946, '#skF_5') | '#skF_2'(B_1946, B_1946, '#skF_5')!=B_1946 | '#skF_1'(B_1946, B_1946, '#skF_5')=B_1946)), inference(superposition, [status(thm), theory('equality')], [c_723, c_89])).
% 5.66/2.27  tff(c_40, plain, (![B_17, A_16]: (~r1_tarski(B_17, A_16) | ~r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.66/2.27  tff(c_3804, plain, (![B_6986]: (~r1_tarski('#skF_5', B_6986) | '#skF_2'(B_6986, B_6986, '#skF_5')!=B_6986 | '#skF_1'(B_6986, B_6986, '#skF_5')=B_6986)), inference(resolution, [status(thm)], [c_1578, c_40])).
% 5.66/2.27  tff(c_3808, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_5')!='#skF_5' | '#skF_1'('#skF_5', '#skF_5', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_6, c_3804])).
% 5.66/2.27  tff(c_3950, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_5')!='#skF_5'), inference(splitLeft, [status(thm)], [c_3808])).
% 5.66/2.27  tff(c_5442, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5289, c_3950])).
% 5.66/2.27  tff(c_5443, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_4873])).
% 5.66/2.27  tff(c_163, plain, (![D_48, B_49, A_50]: (D_48=B_49 | D_48=A_50 | ~r2_hidden(D_48, k2_tarski(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.66/2.27  tff(c_172, plain, (![D_48, A_9]: (D_48=A_9 | D_48=A_9 | ~r2_hidden(D_48, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_163])).
% 5.66/2.27  tff(c_5453, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_5443, c_172])).
% 5.66/2.27  tff(c_5499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_5453])).
% 5.66/2.27  tff(c_5501, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3808])).
% 5.66/2.27  tff(c_5500, plain, ('#skF_1'('#skF_5', '#skF_5', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_3808])).
% 5.66/2.27  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | '#skF_2'(A_3, B_4, C_5)!=B_4 | k2_tarski(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.66/2.27  tff(c_5514, plain, (~r2_hidden('#skF_5', '#skF_5') | '#skF_2'('#skF_5', '#skF_5', '#skF_5')!='#skF_5' | k2_tarski('#skF_5', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_5500, c_14])).
% 5.66/2.27  tff(c_5527, plain, (~r2_hidden('#skF_5', '#skF_5') | '#skF_2'('#skF_5', '#skF_5', '#skF_5')!='#skF_5' | k1_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_5514])).
% 5.66/2.27  tff(c_5539, plain, (~r2_hidden('#skF_5', '#skF_5') | k1_tarski('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_5501, c_5527])).
% 5.66/2.27  tff(c_5540, plain, (~r2_hidden('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_5539])).
% 5.66/2.27  tff(c_7780, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7681, c_5540])).
% 5.66/2.27  tff(c_7940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_7780])).
% 5.66/2.27  tff(c_7941, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_7460])).
% 5.66/2.27  tff(c_7951, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_7941, c_172])).
% 5.66/2.27  tff(c_7997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_44, c_7951])).
% 5.66/2.27  tff(c_7998, plain, (k1_tarski('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_5539])).
% 5.66/2.27  tff(c_96, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.66/2.27  tff(c_110, plain, (![A_9]: (~r1_tarski(k1_tarski(A_9), A_9))), inference(resolution, [status(thm)], [c_89, c_96])).
% 5.66/2.27  tff(c_8013, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7998, c_110])).
% 5.66/2.27  tff(c_8058, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8013])).
% 5.66/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.27  
% 5.66/2.27  Inference rules
% 5.66/2.27  ----------------------
% 5.66/2.27  #Ref     : 0
% 5.66/2.27  #Sup     : 1647
% 5.66/2.27  #Fact    : 32
% 5.66/2.27  #Define  : 0
% 5.66/2.27  #Split   : 23
% 5.66/2.27  #Chain   : 0
% 5.66/2.27  #Close   : 0
% 5.66/2.27  
% 5.66/2.27  Ordering : KBO
% 5.66/2.27  
% 5.66/2.27  Simplification rules
% 5.66/2.27  ----------------------
% 5.66/2.27  #Subsume      : 553
% 5.66/2.27  #Demod        : 290
% 5.66/2.27  #Tautology    : 382
% 5.66/2.27  #SimpNegUnit  : 88
% 5.66/2.27  #BackRed      : 8
% 5.66/2.27  
% 5.66/2.27  #Partial instantiations: 6556
% 5.66/2.27  #Strategies tried      : 1
% 5.66/2.27  
% 5.66/2.27  Timing (in seconds)
% 5.66/2.27  ----------------------
% 5.66/2.27  Preprocessing        : 0.29
% 5.66/2.27  Parsing              : 0.14
% 5.66/2.27  CNF conversion       : 0.02
% 5.66/2.27  Main loop            : 1.07
% 5.66/2.27  Inferencing          : 0.53
% 5.66/2.27  Reduction            : 0.25
% 5.66/2.27  Demodulation         : 0.17
% 5.66/2.27  BG Simplification    : 0.04
% 5.66/2.27  Subsumption          : 0.17
% 5.66/2.27  Abstraction          : 0.06
% 5.66/2.27  MUC search           : 0.00
% 5.66/2.27  Cooper               : 0.00
% 5.66/2.27  Total                : 1.39
% 5.66/2.27  Index Insertion      : 0.00
% 5.66/2.27  Index Deletion       : 0.00
% 5.66/2.27  Index Matching       : 0.00
% 5.66/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

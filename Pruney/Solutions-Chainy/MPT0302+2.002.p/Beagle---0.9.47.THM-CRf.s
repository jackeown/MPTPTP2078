%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:46 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 134 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 235 expanded)
%              Number of equality atoms :   20 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_86,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_80,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_58,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1108,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( r2_hidden(k4_tarski(A_124,B_125),k2_zfmisc_1(C_126,D_127))
      | ~ r2_hidden(B_125,D_127)
      | ~ r2_hidden(A_124,C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_64,plain,(
    k2_zfmisc_1('#skF_7','#skF_6') = k2_zfmisc_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_780,plain,(
    ! [A_89,C_90,B_91,D_92] :
      ( r2_hidden(A_89,C_90)
      | ~ r2_hidden(k4_tarski(A_89,B_91),k2_zfmisc_1(C_90,D_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_783,plain,(
    ! [A_89,B_91] :
      ( r2_hidden(A_89,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_89,B_91),k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_780])).

tff(c_1134,plain,(
    ! [A_124,B_125] :
      ( r2_hidden(A_124,'#skF_7')
      | ~ r2_hidden(B_125,'#skF_7')
      | ~ r2_hidden(A_124,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1108,c_783])).

tff(c_1866,plain,(
    ! [B_177] : ~ r2_hidden(B_177,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1134])).

tff(c_1897,plain,(
    ! [B_179] : r1_tarski('#skF_7',B_179) ),
    inference(resolution,[status(thm)],[c_8,c_1866])).

tff(c_32,plain,(
    ! [A_16,B_17] :
      ( r2_xboole_0(A_16,B_17)
      | B_17 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_44,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_5'(A_23,B_24),B_24)
      | ~ r2_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    ! [A_30] : k5_xboole_0(A_30,k1_xboole_0) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_120,plain,(
    ! [A_47,B_48] : r1_xboole_0(k3_xboole_0(A_47,B_48),k5_xboole_0(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_132,plain,(
    ! [A_30] : r1_xboole_0(k3_xboole_0(A_30,k1_xboole_0),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_134,plain,(
    ! [A_49] : r1_xboole_0(k3_xboole_0(A_49,k1_xboole_0),A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_120])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [A_49] : k3_xboole_0(k3_xboole_0(A_49,k1_xboole_0),A_49) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_134,c_28])).

tff(c_563,plain,(
    ! [A_77,B_78,C_79] :
      ( ~ r1_xboole_0(A_77,B_78)
      | ~ r2_hidden(C_79,k3_xboole_0(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_589,plain,(
    ! [A_49,C_79] :
      ( ~ r1_xboole_0(k3_xboole_0(A_49,k1_xboole_0),A_49)
      | ~ r2_hidden(C_79,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_563])).

tff(c_604,plain,(
    ! [C_80] : ~ r2_hidden(C_80,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_589])).

tff(c_615,plain,(
    ! [A_81] : ~ r2_xboole_0(A_81,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_604])).

tff(c_620,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_615])).

tff(c_1904,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1897,c_620])).

tff(c_1912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1904])).

tff(c_1914,plain,(
    ! [A_180] :
      ( r2_hidden(A_180,'#skF_7')
      | ~ r2_hidden(A_180,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_1134])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3477,plain,(
    ! [A_250] :
      ( r1_tarski(A_250,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_250,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1914,c_6])).

tff(c_3482,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_8,c_3477])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1233,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(k4_tarski(A_138,B_139),k2_zfmisc_1('#skF_6','#skF_7'))
      | ~ r2_hidden(B_139,'#skF_6')
      | ~ r2_hidden(A_138,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1108])).

tff(c_56,plain,(
    ! [A_31,C_33,B_32,D_34] :
      ( r2_hidden(A_31,C_33)
      | ~ r2_hidden(k4_tarski(A_31,B_32),k2_zfmisc_1(C_33,D_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1255,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(A_138,'#skF_6')
      | ~ r2_hidden(B_139,'#skF_6')
      | ~ r2_hidden(A_138,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1233,c_56])).

tff(c_1579,plain,(
    ! [B_156] : ~ r2_hidden(B_156,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1255])).

tff(c_1610,plain,(
    ! [B_158] : r1_tarski('#skF_6',B_158) ),
    inference(resolution,[status(thm)],[c_8,c_1579])).

tff(c_1617,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1610,c_620])).

tff(c_1625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1617])).

tff(c_1627,plain,(
    ! [A_159] :
      ( r2_hidden(A_159,'#skF_6')
      | ~ r2_hidden(A_159,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1255])).

tff(c_6417,plain,(
    ! [A_342] :
      ( r2_hidden('#skF_5'(A_342,'#skF_7'),'#skF_6')
      | ~ r2_xboole_0(A_342,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_44,c_1627])).

tff(c_42,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_5'(A_23,B_24),A_23)
      | ~ r2_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6434,plain,(
    ~ r2_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_6417,c_42])).

tff(c_6437,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_6434])).

tff(c_6440,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_6437])).

tff(c_6442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.18  
% 5.89/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.18  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 5.89/2.18  
% 5.89/2.18  %Foreground sorts:
% 5.89/2.18  
% 5.89/2.18  
% 5.89/2.18  %Background operators:
% 5.89/2.18  
% 5.89/2.18  
% 5.89/2.18  %Foreground operators:
% 5.89/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.89/2.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.89/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/2.18  tff('#skF_7', type, '#skF_7': $i).
% 5.89/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.89/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.89/2.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.89/2.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.89/2.18  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 5.89/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.89/2.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.89/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.89/2.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.89/2.18  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.89/2.18  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.89/2.18  
% 5.89/2.19  tff(f_101, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 5.89/2.19  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.89/2.19  tff(f_92, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.89/2.19  tff(f_54, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 5.89/2.19  tff(f_78, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_0)).
% 5.89/2.19  tff(f_86, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.89/2.19  tff(f_80, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 5.89/2.19  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.89/2.19  tff(f_68, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 5.89/2.19  tff(c_58, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.19  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.89/2.19  tff(c_60, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.19  tff(c_1108, plain, (![A_124, B_125, C_126, D_127]: (r2_hidden(k4_tarski(A_124, B_125), k2_zfmisc_1(C_126, D_127)) | ~r2_hidden(B_125, D_127) | ~r2_hidden(A_124, C_126))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.89/2.19  tff(c_64, plain, (k2_zfmisc_1('#skF_7', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.19  tff(c_780, plain, (![A_89, C_90, B_91, D_92]: (r2_hidden(A_89, C_90) | ~r2_hidden(k4_tarski(A_89, B_91), k2_zfmisc_1(C_90, D_92)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.89/2.19  tff(c_783, plain, (![A_89, B_91]: (r2_hidden(A_89, '#skF_7') | ~r2_hidden(k4_tarski(A_89, B_91), k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_780])).
% 5.89/2.19  tff(c_1134, plain, (![A_124, B_125]: (r2_hidden(A_124, '#skF_7') | ~r2_hidden(B_125, '#skF_7') | ~r2_hidden(A_124, '#skF_6'))), inference(resolution, [status(thm)], [c_1108, c_783])).
% 5.89/2.19  tff(c_1866, plain, (![B_177]: (~r2_hidden(B_177, '#skF_7'))), inference(splitLeft, [status(thm)], [c_1134])).
% 5.89/2.19  tff(c_1897, plain, (![B_179]: (r1_tarski('#skF_7', B_179))), inference(resolution, [status(thm)], [c_8, c_1866])).
% 5.89/2.19  tff(c_32, plain, (![A_16, B_17]: (r2_xboole_0(A_16, B_17) | B_17=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.89/2.19  tff(c_44, plain, (![A_23, B_24]: (r2_hidden('#skF_5'(A_23, B_24), B_24) | ~r2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.89/2.19  tff(c_50, plain, (![A_30]: (k5_xboole_0(A_30, k1_xboole_0)=A_30)), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.89/2.19  tff(c_120, plain, (![A_47, B_48]: (r1_xboole_0(k3_xboole_0(A_47, B_48), k5_xboole_0(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.89/2.19  tff(c_132, plain, (![A_30]: (r1_xboole_0(k3_xboole_0(A_30, k1_xboole_0), A_30))), inference(superposition, [status(thm), theory('equality')], [c_50, c_120])).
% 5.89/2.19  tff(c_134, plain, (![A_49]: (r1_xboole_0(k3_xboole_0(A_49, k1_xboole_0), A_49))), inference(superposition, [status(thm), theory('equality')], [c_50, c_120])).
% 5.89/2.19  tff(c_28, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.89/2.19  tff(c_146, plain, (![A_49]: (k3_xboole_0(k3_xboole_0(A_49, k1_xboole_0), A_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_134, c_28])).
% 5.89/2.19  tff(c_563, plain, (![A_77, B_78, C_79]: (~r1_xboole_0(A_77, B_78) | ~r2_hidden(C_79, k3_xboole_0(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.89/2.19  tff(c_589, plain, (![A_49, C_79]: (~r1_xboole_0(k3_xboole_0(A_49, k1_xboole_0), A_49) | ~r2_hidden(C_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_146, c_563])).
% 5.89/2.19  tff(c_604, plain, (![C_80]: (~r2_hidden(C_80, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_589])).
% 5.89/2.19  tff(c_615, plain, (![A_81]: (~r2_xboole_0(A_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_44, c_604])).
% 5.89/2.19  tff(c_620, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_615])).
% 5.89/2.19  tff(c_1904, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1897, c_620])).
% 5.89/2.19  tff(c_1912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1904])).
% 5.89/2.19  tff(c_1914, plain, (![A_180]: (r2_hidden(A_180, '#skF_7') | ~r2_hidden(A_180, '#skF_6'))), inference(splitRight, [status(thm)], [c_1134])).
% 5.89/2.19  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.89/2.19  tff(c_3477, plain, (![A_250]: (r1_tarski(A_250, '#skF_7') | ~r2_hidden('#skF_1'(A_250, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_1914, c_6])).
% 5.89/2.19  tff(c_3482, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_8, c_3477])).
% 5.89/2.19  tff(c_62, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.89/2.19  tff(c_1233, plain, (![A_138, B_139]: (r2_hidden(k4_tarski(A_138, B_139), k2_zfmisc_1('#skF_6', '#skF_7')) | ~r2_hidden(B_139, '#skF_6') | ~r2_hidden(A_138, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1108])).
% 5.89/2.19  tff(c_56, plain, (![A_31, C_33, B_32, D_34]: (r2_hidden(A_31, C_33) | ~r2_hidden(k4_tarski(A_31, B_32), k2_zfmisc_1(C_33, D_34)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.89/2.19  tff(c_1255, plain, (![A_138, B_139]: (r2_hidden(A_138, '#skF_6') | ~r2_hidden(B_139, '#skF_6') | ~r2_hidden(A_138, '#skF_7'))), inference(resolution, [status(thm)], [c_1233, c_56])).
% 5.89/2.19  tff(c_1579, plain, (![B_156]: (~r2_hidden(B_156, '#skF_6'))), inference(splitLeft, [status(thm)], [c_1255])).
% 5.89/2.19  tff(c_1610, plain, (![B_158]: (r1_tarski('#skF_6', B_158))), inference(resolution, [status(thm)], [c_8, c_1579])).
% 5.89/2.19  tff(c_1617, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1610, c_620])).
% 5.89/2.19  tff(c_1625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1617])).
% 5.89/2.19  tff(c_1627, plain, (![A_159]: (r2_hidden(A_159, '#skF_6') | ~r2_hidden(A_159, '#skF_7'))), inference(splitRight, [status(thm)], [c_1255])).
% 5.89/2.19  tff(c_6417, plain, (![A_342]: (r2_hidden('#skF_5'(A_342, '#skF_7'), '#skF_6') | ~r2_xboole_0(A_342, '#skF_7'))), inference(resolution, [status(thm)], [c_44, c_1627])).
% 5.89/2.19  tff(c_42, plain, (![A_23, B_24]: (~r2_hidden('#skF_5'(A_23, B_24), A_23) | ~r2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.89/2.19  tff(c_6434, plain, (~r2_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_6417, c_42])).
% 5.89/2.19  tff(c_6437, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_32, c_6434])).
% 5.89/2.19  tff(c_6440, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3482, c_6437])).
% 5.89/2.19  tff(c_6442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_6440])).
% 5.89/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.89/2.19  
% 5.89/2.19  Inference rules
% 5.89/2.19  ----------------------
% 5.89/2.19  #Ref     : 1
% 5.89/2.19  #Sup     : 1521
% 5.89/2.19  #Fact    : 0
% 5.89/2.19  #Define  : 0
% 5.89/2.19  #Split   : 12
% 5.89/2.19  #Chain   : 0
% 5.89/2.19  #Close   : 0
% 5.89/2.19  
% 5.89/2.19  Ordering : KBO
% 5.89/2.19  
% 5.89/2.19  Simplification rules
% 5.89/2.19  ----------------------
% 5.89/2.19  #Subsume      : 516
% 5.89/2.19  #Demod        : 556
% 5.89/2.19  #Tautology    : 543
% 5.89/2.19  #SimpNegUnit  : 79
% 5.89/2.19  #BackRed      : 28
% 5.89/2.19  
% 5.89/2.19  #Partial instantiations: 0
% 5.89/2.19  #Strategies tried      : 1
% 5.89/2.19  
% 5.89/2.19  Timing (in seconds)
% 5.89/2.19  ----------------------
% 5.89/2.20  Preprocessing        : 0.37
% 5.89/2.20  Parsing              : 0.19
% 5.89/2.20  CNF conversion       : 0.03
% 5.89/2.20  Main loop            : 1.06
% 5.89/2.20  Inferencing          : 0.34
% 5.89/2.20  Reduction            : 0.39
% 5.89/2.20  Demodulation         : 0.29
% 5.89/2.20  BG Simplification    : 0.04
% 5.89/2.20  Subsumption          : 0.22
% 5.89/2.20  Abstraction          : 0.04
% 5.89/2.20  MUC search           : 0.00
% 5.89/2.20  Cooper               : 0.00
% 5.89/2.20  Total                : 1.46
% 5.89/2.20  Index Insertion      : 0.00
% 5.89/2.20  Index Deletion       : 0.00
% 5.89/2.20  Index Matching       : 0.00
% 5.89/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:13 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 126 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :  122 ( 255 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D)
        & r1_xboole_0(B,D) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(c_12,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_tarski(A_23),B_24)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_65,plain,(
    ! [B_30,A_31] :
      ( r1_xboole_0(B_30,A_31)
      | ~ r1_xboole_0(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_68,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_1853,plain,(
    ! [A_210,C_211,B_212,D_213] :
      ( r1_xboole_0(A_210,C_211)
      | ~ r1_xboole_0(B_212,D_213)
      | ~ r1_tarski(C_211,D_213)
      | ~ r1_tarski(A_210,B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1867,plain,(
    ! [A_210,C_211] :
      ( r1_xboole_0(A_210,C_211)
      | ~ r1_tarski(C_211,'#skF_3')
      | ~ r1_tarski(A_210,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_68,c_1853])).

tff(c_100,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | ~ r1_tarski(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_113,plain,(
    ! [A_38] : r2_hidden(A_38,k1_tarski(A_38)) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_125,plain,(
    ! [A_45,B_46] :
      ( r1_xboole_0(A_45,B_46)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    ! [B_46,A_45] :
      ( r1_xboole_0(B_46,A_45)
      | k3_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_125,c_6])).

tff(c_338,plain,(
    ! [A_88,C_89,B_90] :
      ( ~ r1_xboole_0(A_88,C_89)
      | ~ r1_xboole_0(A_88,B_90)
      | r1_xboole_0(A_88,k2_xboole_0(B_90,C_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_620,plain,(
    ! [B_113,C_114,A_115] :
      ( r1_xboole_0(k2_xboole_0(B_113,C_114),A_115)
      | ~ r1_xboole_0(A_115,C_114)
      | ~ r1_xboole_0(A_115,B_113) ) ),
    inference(resolution,[status(thm)],[c_338,c_6])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_650,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_620,c_42])).

tff(c_661,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_650])).

tff(c_678,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_135,c_661])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_26,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_522,plain,(
    ! [B_103,C_104,A_105] :
      ( k2_tarski(B_103,C_104) = A_105
      | k1_tarski(C_104) = A_105
      | k1_tarski(B_103) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k2_tarski(B_103,C_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_538,plain,(
    ! [A_19,A_105] :
      ( k2_tarski(A_19,A_19) = A_105
      | k1_tarski(A_19) = A_105
      | k1_tarski(A_19) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_tarski(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_522])).

tff(c_1689,plain,(
    ! [A_179,A_180] :
      ( k1_tarski(A_179) = A_180
      | k1_tarski(A_179) = A_180
      | k1_tarski(A_179) = A_180
      | k1_xboole_0 = A_180
      | ~ r1_tarski(A_180,k1_tarski(A_179)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_538])).

tff(c_1696,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_1689])).

tff(c_1707,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_1696])).

tff(c_180,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_198,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | ~ r1_tarski(k1_tarski('#skF_4'),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_180])).

tff(c_212,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_216,plain,(
    ~ r2_hidden('#skF_4',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_212])).

tff(c_1714,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1707,c_216])).

tff(c_1719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1714])).

tff(c_1720,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_1776,plain,(
    ! [A_200,B_201,C_202] :
      ( ~ r1_xboole_0(A_200,k3_xboole_0(B_201,C_202))
      | ~ r1_tarski(A_200,C_202)
      | r1_xboole_0(A_200,B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2143,plain,(
    ! [A_231] :
      ( ~ r1_xboole_0(A_231,k1_tarski('#skF_4'))
      | ~ r1_tarski(A_231,'#skF_2')
      | r1_xboole_0(A_231,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1720,c_1776])).

tff(c_2165,plain,(
    ! [A_210] :
      ( r1_xboole_0(A_210,'#skF_1')
      | ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3')
      | ~ r1_tarski(A_210,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1867,c_2143])).

tff(c_2243,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2165])).

tff(c_2247,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_2243])).

tff(c_2251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2247])).

tff(c_2320,plain,(
    ! [A_243] :
      ( r1_xboole_0(A_243,'#skF_1')
      | ~ r1_tarski(A_243,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_2165])).

tff(c_1757,plain,(
    ! [A_188,C_189,B_190] :
      ( ~ r1_xboole_0(A_188,C_189)
      | ~ r1_xboole_0(A_188,B_190)
      | r1_xboole_0(A_188,k2_xboole_0(B_190,C_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2081,plain,(
    ! [B_228,C_229,A_230] :
      ( r1_xboole_0(k2_xboole_0(B_228,C_229),A_230)
      | ~ r1_xboole_0(A_230,C_229)
      | ~ r1_xboole_0(A_230,B_228) ) ),
    inference(resolution,[status(thm)],[c_1757,c_6])).

tff(c_2111,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_2081,c_42])).

tff(c_2122,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2111])).

tff(c_2323,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2320,c_2122])).

tff(c_2334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.77  
% 4.51/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.77  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.51/1.77  
% 4.51/1.77  %Foreground sorts:
% 4.51/1.77  
% 4.51/1.77  
% 4.51/1.77  %Background operators:
% 4.51/1.77  
% 4.51/1.77  
% 4.51/1.77  %Foreground operators:
% 4.51/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.51/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.51/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.51/1.77  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.51/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.51/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.77  tff('#skF_1', type, '#skF_1': $i).
% 4.51/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.51/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.51/1.77  
% 4.60/1.79  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.60/1.79  tff(f_103, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 4.60/1.79  tff(f_94, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 4.60/1.79  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.60/1.79  tff(f_49, axiom, (![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 4.60/1.79  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.60/1.79  tff(f_65, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.60/1.79  tff(f_75, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.60/1.79  tff(f_90, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.60/1.79  tff(f_73, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 4.60/1.79  tff(c_12, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.79  tff(c_46, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.60/1.79  tff(c_40, plain, (![A_23, B_24]: (r1_tarski(k1_tarski(A_23), B_24) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.60/1.79  tff(c_44, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.60/1.79  tff(c_65, plain, (![B_30, A_31]: (r1_xboole_0(B_30, A_31) | ~r1_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.79  tff(c_68, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_65])).
% 4.60/1.79  tff(c_1853, plain, (![A_210, C_211, B_212, D_213]: (r1_xboole_0(A_210, C_211) | ~r1_xboole_0(B_212, D_213) | ~r1_tarski(C_211, D_213) | ~r1_tarski(A_210, B_212))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.79  tff(c_1867, plain, (![A_210, C_211]: (r1_xboole_0(A_210, C_211) | ~r1_tarski(C_211, '#skF_3') | ~r1_tarski(A_210, '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_1853])).
% 4.60/1.79  tff(c_100, plain, (![A_38, B_39]: (r2_hidden(A_38, B_39) | ~r1_tarski(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.60/1.79  tff(c_113, plain, (![A_38]: (r2_hidden(A_38, k1_tarski(A_38)))), inference(resolution, [status(thm)], [c_12, c_100])).
% 4.60/1.79  tff(c_125, plain, (![A_45, B_46]: (r1_xboole_0(A_45, B_46) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.60/1.79  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.60/1.79  tff(c_135, plain, (![B_46, A_45]: (r1_xboole_0(B_46, A_45) | k3_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_125, c_6])).
% 4.60/1.79  tff(c_338, plain, (![A_88, C_89, B_90]: (~r1_xboole_0(A_88, C_89) | ~r1_xboole_0(A_88, B_90) | r1_xboole_0(A_88, k2_xboole_0(B_90, C_89)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.60/1.79  tff(c_620, plain, (![B_113, C_114, A_115]: (r1_xboole_0(k2_xboole_0(B_113, C_114), A_115) | ~r1_xboole_0(A_115, C_114) | ~r1_xboole_0(A_115, B_113))), inference(resolution, [status(thm)], [c_338, c_6])).
% 4.60/1.79  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.60/1.79  tff(c_650, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_620, c_42])).
% 4.60/1.79  tff(c_661, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_650])).
% 4.60/1.79  tff(c_678, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_135, c_661])).
% 4.60/1.79  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.60/1.79  tff(c_26, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.60/1.79  tff(c_522, plain, (![B_103, C_104, A_105]: (k2_tarski(B_103, C_104)=A_105 | k1_tarski(C_104)=A_105 | k1_tarski(B_103)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k2_tarski(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.60/1.79  tff(c_538, plain, (![A_19, A_105]: (k2_tarski(A_19, A_19)=A_105 | k1_tarski(A_19)=A_105 | k1_tarski(A_19)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_522])).
% 4.60/1.79  tff(c_1689, plain, (![A_179, A_180]: (k1_tarski(A_179)=A_180 | k1_tarski(A_179)=A_180 | k1_tarski(A_179)=A_180 | k1_xboole_0=A_180 | ~r1_tarski(A_180, k1_tarski(A_179)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_538])).
% 4.60/1.79  tff(c_1696, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_1689])).
% 4.60/1.79  tff(c_1707, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_678, c_1696])).
% 4.60/1.79  tff(c_180, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.79  tff(c_198, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4') | ~r1_tarski(k1_tarski('#skF_4'), k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_180])).
% 4.60/1.79  tff(c_212, plain, (~r1_tarski(k1_tarski('#skF_4'), k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_198])).
% 4.60/1.79  tff(c_216, plain, (~r2_hidden('#skF_4', k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_212])).
% 4.60/1.79  tff(c_1714, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1707, c_216])).
% 4.60/1.79  tff(c_1719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_1714])).
% 4.60/1.79  tff(c_1720, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_198])).
% 4.60/1.79  tff(c_1776, plain, (![A_200, B_201, C_202]: (~r1_xboole_0(A_200, k3_xboole_0(B_201, C_202)) | ~r1_tarski(A_200, C_202) | r1_xboole_0(A_200, B_201))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.60/1.79  tff(c_2143, plain, (![A_231]: (~r1_xboole_0(A_231, k1_tarski('#skF_4')) | ~r1_tarski(A_231, '#skF_2') | r1_xboole_0(A_231, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1720, c_1776])).
% 4.60/1.79  tff(c_2165, plain, (![A_210]: (r1_xboole_0(A_210, '#skF_1') | ~r1_tarski(k1_tarski('#skF_4'), '#skF_3') | ~r1_tarski(A_210, '#skF_2'))), inference(resolution, [status(thm)], [c_1867, c_2143])).
% 4.60/1.79  tff(c_2243, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2165])).
% 4.60/1.79  tff(c_2247, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_2243])).
% 4.60/1.79  tff(c_2251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_2247])).
% 4.60/1.79  tff(c_2320, plain, (![A_243]: (r1_xboole_0(A_243, '#skF_1') | ~r1_tarski(A_243, '#skF_2'))), inference(splitRight, [status(thm)], [c_2165])).
% 4.60/1.79  tff(c_1757, plain, (![A_188, C_189, B_190]: (~r1_xboole_0(A_188, C_189) | ~r1_xboole_0(A_188, B_190) | r1_xboole_0(A_188, k2_xboole_0(B_190, C_189)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.60/1.79  tff(c_2081, plain, (![B_228, C_229, A_230]: (r1_xboole_0(k2_xboole_0(B_228, C_229), A_230) | ~r1_xboole_0(A_230, C_229) | ~r1_xboole_0(A_230, B_228))), inference(resolution, [status(thm)], [c_1757, c_6])).
% 4.60/1.79  tff(c_2111, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_2081, c_42])).
% 4.60/1.79  tff(c_2122, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2111])).
% 4.60/1.79  tff(c_2323, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2320, c_2122])).
% 4.60/1.79  tff(c_2334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2323])).
% 4.60/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.79  
% 4.60/1.79  Inference rules
% 4.60/1.79  ----------------------
% 4.60/1.79  #Ref     : 0
% 4.60/1.79  #Sup     : 541
% 4.60/1.79  #Fact    : 0
% 4.60/1.79  #Define  : 0
% 4.60/1.79  #Split   : 14
% 4.60/1.79  #Chain   : 0
% 4.60/1.79  #Close   : 0
% 4.60/1.79  
% 4.60/1.79  Ordering : KBO
% 4.60/1.79  
% 4.60/1.79  Simplification rules
% 4.60/1.79  ----------------------
% 4.60/1.79  #Subsume      : 77
% 4.60/1.79  #Demod        : 105
% 4.60/1.79  #Tautology    : 155
% 4.60/1.79  #SimpNegUnit  : 2
% 4.60/1.79  #BackRed      : 6
% 4.60/1.79  
% 4.60/1.79  #Partial instantiations: 0
% 4.60/1.79  #Strategies tried      : 1
% 4.60/1.79  
% 4.60/1.79  Timing (in seconds)
% 4.60/1.79  ----------------------
% 4.60/1.79  Preprocessing        : 0.31
% 4.60/1.79  Parsing              : 0.16
% 4.60/1.79  CNF conversion       : 0.02
% 4.60/1.79  Main loop            : 0.72
% 4.60/1.79  Inferencing          : 0.25
% 4.60/1.79  Reduction            : 0.20
% 4.60/1.79  Demodulation         : 0.14
% 4.60/1.79  BG Simplification    : 0.03
% 4.60/1.79  Subsumption          : 0.19
% 4.60/1.79  Abstraction          : 0.03
% 4.60/1.79  MUC search           : 0.00
% 4.60/1.79  Cooper               : 0.00
% 4.60/1.79  Total                : 1.06
% 4.60/1.79  Index Insertion      : 0.00
% 4.60/1.79  Index Deletion       : 0.00
% 4.60/1.79  Index Matching       : 0.00
% 4.60/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------

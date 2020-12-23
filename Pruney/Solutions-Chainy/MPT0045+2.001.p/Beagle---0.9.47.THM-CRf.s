%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 340 expanded)
%              Number of leaves         :   16 ( 120 expanded)
%              Depth                    :   19
%              Number of atoms          :  107 ( 870 expanded)
%              Number of equality atoms :   24 (  98 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_554,plain,(
    ! [A_103,B_104,C_105] :
      ( ~ r2_hidden('#skF_2'(A_103,B_104,C_105),B_104)
      | r2_hidden('#skF_3'(A_103,B_104,C_105),C_105)
      | k4_xboole_0(A_103,B_104) = C_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_563,plain,(
    ! [A_106,C_107] :
      ( r2_hidden('#skF_3'(A_106,A_106,C_107),C_107)
      | k4_xboole_0(A_106,A_106) = C_107 ) ),
    inference(resolution,[status(thm)],[c_24,c_554])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_1'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_92,plain,(
    ! [A_34,B_35,B_36] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_34,B_35),B_36),A_34)
      | r1_tarski(k4_xboole_0(A_34,B_35),B_36) ) ),
    inference(resolution,[status(thm)],[c_34,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_34,B_35] : r1_tarski(k4_xboole_0(A_34,B_35),A_34) ),
    inference(resolution,[status(thm)],[c_92,c_4])).

tff(c_30,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [C_25,B_26,A_27] :
      ( r2_hidden(C_25,B_26)
      | ~ r2_hidden(C_25,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_73,plain,(
    ! [A_31,B_32,B_33] :
      ( r2_hidden('#skF_1'(A_31,B_32),B_33)
      | ~ r1_tarski(A_31,B_33)
      | r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_6,c_52])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_146,plain,(
    ! [A_50,B_51,B_52,A_53] :
      ( ~ r2_hidden('#skF_1'(A_50,B_51),B_52)
      | ~ r1_tarski(A_50,k4_xboole_0(A_53,B_52))
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_160,plain,(
    ! [A_54,A_55,B_56] :
      ( ~ r1_tarski(A_54,k4_xboole_0(A_55,A_54))
      | r1_tarski(A_54,B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_171,plain,(
    ! [B_56] : r1_tarski('#skF_4',B_56) ),
    inference(resolution,[status(thm)],[c_30,c_160])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_254,plain,(
    ! [A_74,B_75,B_76,B_77] :
      ( r2_hidden('#skF_1'(A_74,B_75),B_76)
      | ~ r1_tarski(B_77,B_76)
      | ~ r1_tarski(A_74,B_77)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_73,c_2])).

tff(c_368,plain,(
    ! [A_88,B_89,B_90] :
      ( r2_hidden('#skF_1'(A_88,B_89),B_90)
      | ~ r1_tarski(A_88,'#skF_4')
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_171,c_254])).

tff(c_433,plain,(
    ! [A_93,B_94] :
      ( ~ r1_tarski(A_93,'#skF_4')
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_368,c_4])).

tff(c_463,plain,(
    ! [B_95,B_96] : r1_tarski(k4_xboole_0('#skF_4',B_95),B_96) ),
    inference(resolution,[status(thm)],[c_108,c_433])).

tff(c_56,plain,(
    ! [D_28,A_29,B_30] :
      ( r2_hidden(D_28,k4_xboole_0(A_29,B_30))
      | r2_hidden(D_28,B_30)
      | ~ r2_hidden(D_28,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [D_28,B_2,A_29,B_30] :
      ( r2_hidden(D_28,B_2)
      | ~ r1_tarski(k4_xboole_0(A_29,B_30),B_2)
      | r2_hidden(D_28,B_30)
      | ~ r2_hidden(D_28,A_29) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_494,plain,(
    ! [D_28,B_96,B_95] :
      ( r2_hidden(D_28,B_96)
      | r2_hidden(D_28,B_95)
      | ~ r2_hidden(D_28,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_463,c_69])).

tff(c_580,plain,(
    ! [A_106,B_96,B_95] :
      ( r2_hidden('#skF_3'(A_106,A_106,'#skF_4'),B_96)
      | r2_hidden('#skF_3'(A_106,A_106,'#skF_4'),B_95)
      | k4_xboole_0(A_106,A_106) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_563,c_494])).

tff(c_755,plain,(
    ! [A_106,B_96] :
      ( k4_xboole_0(A_106,A_106) = '#skF_4'
      | r2_hidden('#skF_3'(A_106,A_106,'#skF_4'),B_96) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_580])).

tff(c_800,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,A_132) = '#skF_4'
      | r2_hidden('#skF_3'(A_132,A_132,'#skF_4'),B_133) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_580])).

tff(c_822,plain,(
    ! [A_134,B_135] :
      ( ~ r2_hidden('#skF_3'(A_134,A_134,'#skF_4'),B_135)
      | k4_xboole_0(A_134,A_134) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_800,c_10])).

tff(c_848,plain,(
    ! [A_106] : k4_xboole_0(A_106,A_106) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_755,c_822])).

tff(c_270,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_2'(A_78,B_79,C_80),A_78)
      | r2_hidden('#skF_3'(A_78,B_79,C_80),C_80)
      | k4_xboole_0(A_78,B_79) = C_80 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k4_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_302,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_3'(A_81,B_82,A_81),A_81)
      | k4_xboole_0(A_81,B_82) = A_81 ) ),
    inference(resolution,[status(thm)],[c_270,c_20])).

tff(c_313,plain,(
    ! [A_81,B_82,B_2] :
      ( r2_hidden('#skF_3'(A_81,B_82,A_81),B_2)
      | ~ r1_tarski(A_81,B_2)
      | k4_xboole_0(A_81,B_82) = A_81 ) ),
    inference(resolution,[status(thm)],[c_302,c_2])).

tff(c_561,plain,(
    ! [A_6,C_8] :
      ( r2_hidden('#skF_3'(A_6,A_6,C_8),C_8)
      | k4_xboole_0(A_6,A_6) = C_8 ) ),
    inference(resolution,[status(thm)],[c_24,c_554])).

tff(c_1160,plain,(
    ! [A_151,C_152] :
      ( r2_hidden('#skF_3'(A_151,A_151,C_152),C_152)
      | C_152 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_561])).

tff(c_865,plain,(
    ! [A_136] : k4_xboole_0(A_136,A_136) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_755,c_822])).

tff(c_906,plain,(
    ! [D_11,A_136] :
      ( ~ r2_hidden(D_11,A_136)
      | ~ r2_hidden(D_11,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_10])).

tff(c_1219,plain,(
    ! [A_158,C_159] :
      ( ~ r2_hidden('#skF_3'(A_158,A_158,C_159),'#skF_4')
      | C_159 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1160,c_906])).

tff(c_1229,plain,(
    ! [B_82] :
      ( B_82 = '#skF_4'
      | ~ r1_tarski(B_82,'#skF_4')
      | k4_xboole_0(B_82,B_82) = B_82 ) ),
    inference(resolution,[status(thm)],[c_313,c_1219])).

tff(c_1243,plain,(
    ! [B_160] :
      ( B_160 = '#skF_4'
      | ~ r1_tarski(B_160,'#skF_4')
      | B_160 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_1229])).

tff(c_1271,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_1243])).

tff(c_1283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_1271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.58  
% 2.92/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.59  %$ r2_hidden > r1_tarski > k4_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.92/1.59  
% 2.92/1.59  %Foreground sorts:
% 2.92/1.59  
% 2.92/1.59  
% 2.92/1.59  %Background operators:
% 2.92/1.59  
% 2.92/1.59  
% 2.92/1.59  %Foreground operators:
% 2.92/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.59  tff('#skF_5', type, '#skF_5': $i).
% 2.92/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.92/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.92/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.92/1.59  
% 2.92/1.60  tff(f_49, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.92/1.60  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.92/1.60  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.92/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.92/1.60  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.60  tff(c_26, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.92/1.60  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.60  tff(c_554, plain, (![A_103, B_104, C_105]: (~r2_hidden('#skF_2'(A_103, B_104, C_105), B_104) | r2_hidden('#skF_3'(A_103, B_104, C_105), C_105) | k4_xboole_0(A_103, B_104)=C_105)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.60  tff(c_563, plain, (![A_106, C_107]: (r2_hidden('#skF_3'(A_106, A_106, C_107), C_107) | k4_xboole_0(A_106, A_106)=C_107)), inference(resolution, [status(thm)], [c_24, c_554])).
% 2.92/1.60  tff(c_34, plain, (![A_20, B_21]: (r2_hidden('#skF_1'(A_20, B_21), A_20) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.60  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.60  tff(c_92, plain, (![A_34, B_35, B_36]: (r2_hidden('#skF_1'(k4_xboole_0(A_34, B_35), B_36), A_34) | r1_tarski(k4_xboole_0(A_34, B_35), B_36))), inference(resolution, [status(thm)], [c_34, c_12])).
% 2.92/1.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.60  tff(c_108, plain, (![A_34, B_35]: (r1_tarski(k4_xboole_0(A_34, B_35), A_34))), inference(resolution, [status(thm)], [c_92, c_4])).
% 2.92/1.60  tff(c_30, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.60  tff(c_52, plain, (![C_25, B_26, A_27]: (r2_hidden(C_25, B_26) | ~r2_hidden(C_25, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.60  tff(c_73, plain, (![A_31, B_32, B_33]: (r2_hidden('#skF_1'(A_31, B_32), B_33) | ~r1_tarski(A_31, B_33) | r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_6, c_52])).
% 2.92/1.60  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.60  tff(c_146, plain, (![A_50, B_51, B_52, A_53]: (~r2_hidden('#skF_1'(A_50, B_51), B_52) | ~r1_tarski(A_50, k4_xboole_0(A_53, B_52)) | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_73, c_10])).
% 2.92/1.60  tff(c_160, plain, (![A_54, A_55, B_56]: (~r1_tarski(A_54, k4_xboole_0(A_55, A_54)) | r1_tarski(A_54, B_56))), inference(resolution, [status(thm)], [c_6, c_146])).
% 2.92/1.60  tff(c_171, plain, (![B_56]: (r1_tarski('#skF_4', B_56))), inference(resolution, [status(thm)], [c_30, c_160])).
% 2.92/1.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.92/1.60  tff(c_254, plain, (![A_74, B_75, B_76, B_77]: (r2_hidden('#skF_1'(A_74, B_75), B_76) | ~r1_tarski(B_77, B_76) | ~r1_tarski(A_74, B_77) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_73, c_2])).
% 2.92/1.60  tff(c_368, plain, (![A_88, B_89, B_90]: (r2_hidden('#skF_1'(A_88, B_89), B_90) | ~r1_tarski(A_88, '#skF_4') | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_171, c_254])).
% 2.92/1.60  tff(c_433, plain, (![A_93, B_94]: (~r1_tarski(A_93, '#skF_4') | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_368, c_4])).
% 2.92/1.60  tff(c_463, plain, (![B_95, B_96]: (r1_tarski(k4_xboole_0('#skF_4', B_95), B_96))), inference(resolution, [status(thm)], [c_108, c_433])).
% 2.92/1.60  tff(c_56, plain, (![D_28, A_29, B_30]: (r2_hidden(D_28, k4_xboole_0(A_29, B_30)) | r2_hidden(D_28, B_30) | ~r2_hidden(D_28, A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.60  tff(c_69, plain, (![D_28, B_2, A_29, B_30]: (r2_hidden(D_28, B_2) | ~r1_tarski(k4_xboole_0(A_29, B_30), B_2) | r2_hidden(D_28, B_30) | ~r2_hidden(D_28, A_29))), inference(resolution, [status(thm)], [c_56, c_2])).
% 2.92/1.60  tff(c_494, plain, (![D_28, B_96, B_95]: (r2_hidden(D_28, B_96) | r2_hidden(D_28, B_95) | ~r2_hidden(D_28, '#skF_4'))), inference(resolution, [status(thm)], [c_463, c_69])).
% 2.92/1.60  tff(c_580, plain, (![A_106, B_96, B_95]: (r2_hidden('#skF_3'(A_106, A_106, '#skF_4'), B_96) | r2_hidden('#skF_3'(A_106, A_106, '#skF_4'), B_95) | k4_xboole_0(A_106, A_106)='#skF_4')), inference(resolution, [status(thm)], [c_563, c_494])).
% 2.92/1.60  tff(c_755, plain, (![A_106, B_96]: (k4_xboole_0(A_106, A_106)='#skF_4' | r2_hidden('#skF_3'(A_106, A_106, '#skF_4'), B_96))), inference(factorization, [status(thm), theory('equality')], [c_580])).
% 2.92/1.60  tff(c_800, plain, (![A_132, B_133]: (k4_xboole_0(A_132, A_132)='#skF_4' | r2_hidden('#skF_3'(A_132, A_132, '#skF_4'), B_133))), inference(factorization, [status(thm), theory('equality')], [c_580])).
% 2.92/1.60  tff(c_822, plain, (![A_134, B_135]: (~r2_hidden('#skF_3'(A_134, A_134, '#skF_4'), B_135) | k4_xboole_0(A_134, A_134)='#skF_4')), inference(resolution, [status(thm)], [c_800, c_10])).
% 2.92/1.60  tff(c_848, plain, (![A_106]: (k4_xboole_0(A_106, A_106)='#skF_4')), inference(resolution, [status(thm)], [c_755, c_822])).
% 2.92/1.60  tff(c_270, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_2'(A_78, B_79, C_80), A_78) | r2_hidden('#skF_3'(A_78, B_79, C_80), C_80) | k4_xboole_0(A_78, B_79)=C_80)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.60  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k4_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.92/1.60  tff(c_302, plain, (![A_81, B_82]: (r2_hidden('#skF_3'(A_81, B_82, A_81), A_81) | k4_xboole_0(A_81, B_82)=A_81)), inference(resolution, [status(thm)], [c_270, c_20])).
% 2.92/1.60  tff(c_313, plain, (![A_81, B_82, B_2]: (r2_hidden('#skF_3'(A_81, B_82, A_81), B_2) | ~r1_tarski(A_81, B_2) | k4_xboole_0(A_81, B_82)=A_81)), inference(resolution, [status(thm)], [c_302, c_2])).
% 2.92/1.60  tff(c_561, plain, (![A_6, C_8]: (r2_hidden('#skF_3'(A_6, A_6, C_8), C_8) | k4_xboole_0(A_6, A_6)=C_8)), inference(resolution, [status(thm)], [c_24, c_554])).
% 2.92/1.60  tff(c_1160, plain, (![A_151, C_152]: (r2_hidden('#skF_3'(A_151, A_151, C_152), C_152) | C_152='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_848, c_561])).
% 2.92/1.60  tff(c_865, plain, (![A_136]: (k4_xboole_0(A_136, A_136)='#skF_4')), inference(resolution, [status(thm)], [c_755, c_822])).
% 2.92/1.60  tff(c_906, plain, (![D_11, A_136]: (~r2_hidden(D_11, A_136) | ~r2_hidden(D_11, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_865, c_10])).
% 2.92/1.60  tff(c_1219, plain, (![A_158, C_159]: (~r2_hidden('#skF_3'(A_158, A_158, C_159), '#skF_4') | C_159='#skF_4')), inference(resolution, [status(thm)], [c_1160, c_906])).
% 2.92/1.60  tff(c_1229, plain, (![B_82]: (B_82='#skF_4' | ~r1_tarski(B_82, '#skF_4') | k4_xboole_0(B_82, B_82)=B_82)), inference(resolution, [status(thm)], [c_313, c_1219])).
% 2.92/1.60  tff(c_1243, plain, (![B_160]: (B_160='#skF_4' | ~r1_tarski(B_160, '#skF_4') | B_160='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_848, c_1229])).
% 2.92/1.60  tff(c_1271, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_26, c_1243])).
% 2.92/1.60  tff(c_1283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_1271])).
% 2.92/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.60  
% 2.92/1.60  Inference rules
% 2.92/1.60  ----------------------
% 2.92/1.60  #Ref     : 0
% 2.92/1.60  #Sup     : 265
% 2.92/1.60  #Fact    : 2
% 2.92/1.60  #Define  : 0
% 2.92/1.60  #Split   : 0
% 2.92/1.60  #Chain   : 0
% 2.92/1.60  #Close   : 0
% 2.92/1.60  
% 2.92/1.60  Ordering : KBO
% 2.92/1.60  
% 2.92/1.60  Simplification rules
% 2.92/1.60  ----------------------
% 2.92/1.60  #Subsume      : 54
% 2.92/1.60  #Demod        : 116
% 2.92/1.60  #Tautology    : 107
% 2.92/1.60  #SimpNegUnit  : 2
% 2.92/1.60  #BackRed      : 4
% 2.92/1.60  
% 2.92/1.60  #Partial instantiations: 0
% 2.92/1.60  #Strategies tried      : 1
% 2.92/1.60  
% 2.92/1.60  Timing (in seconds)
% 2.92/1.60  ----------------------
% 2.92/1.60  Preprocessing        : 0.35
% 2.92/1.60  Parsing              : 0.17
% 2.92/1.60  CNF conversion       : 0.04
% 2.92/1.60  Main loop            : 0.43
% 2.92/1.60  Inferencing          : 0.17
% 2.92/1.60  Reduction            : 0.12
% 2.92/1.60  Demodulation         : 0.08
% 2.92/1.60  BG Simplification    : 0.03
% 2.92/1.61  Subsumption          : 0.10
% 2.92/1.61  Abstraction          : 0.02
% 2.92/1.61  MUC search           : 0.00
% 2.92/1.61  Cooper               : 0.00
% 2.92/1.61  Total                : 0.82
% 2.92/1.61  Index Insertion      : 0.00
% 2.92/1.61  Index Deletion       : 0.00
% 2.92/1.61  Index Matching       : 0.00
% 2.92/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:04 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 127 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 ( 157 expanded)
%              Number of equality atoms :   37 (  92 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_121,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_142,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_121])).

tff(c_150,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_155,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_xboole_0) = k3_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_14])).

tff(c_167,plain,(
    ! [A_36] : k3_xboole_0(A_36,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_155])).

tff(c_149,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_689,plain,(
    ! [A_64,B_65,C_66] : k2_xboole_0(k4_xboole_0(A_64,B_65),k3_xboole_0(A_64,C_66)) = k4_xboole_0(A_64,k4_xboole_0(B_65,C_66)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_736,plain,(
    ! [A_6,C_66] : k4_xboole_0(A_6,k4_xboole_0(A_6,C_66)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(A_6,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_689])).

tff(c_1339,plain,(
    ! [A_81,C_82] : k2_xboole_0(k1_xboole_0,k3_xboole_0(A_81,C_82)) = k3_xboole_0(A_81,C_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_736])).

tff(c_1376,plain,(
    ! [A_36] : k3_xboole_0(A_36,A_36) = k2_xboole_0(k1_xboole_0,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_1339])).

tff(c_1398,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_1376])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_22,B_23] : k2_xboole_0(A_22,k3_xboole_0(A_22,B_23)) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_45])).

tff(c_171,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_xboole_0(A_37,C_38)
      | ~ r1_xboole_0(A_37,k2_xboole_0(B_39,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_294,plain,(
    ! [A_45,A_46] :
      ( r1_xboole_0(A_45,k1_xboole_0)
      | ~ r1_xboole_0(A_45,A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_171])).

tff(c_310,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(A_47,k1_xboole_0)
      | k3_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_294])).

tff(c_319,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_310])).

tff(c_22,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_xboole_0(A_17,C_19)
      | ~ r1_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2248,plain,(
    ! [A_103,A_104,C_105,B_106] :
      ( r1_xboole_0(A_103,k3_xboole_0(A_104,C_105))
      | ~ r1_xboole_0(A_103,k4_xboole_0(A_104,k4_xboole_0(B_106,C_105))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_22])).

tff(c_2304,plain,(
    ! [A_103,B_106,C_105] :
      ( r1_xboole_0(A_103,k3_xboole_0(k4_xboole_0(B_106,C_105),C_105))
      | ~ r1_xboole_0(A_103,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_2248])).

tff(c_2336,plain,(
    ! [A_107,B_108,C_109] : r1_xboole_0(A_107,k3_xboole_0(k4_xboole_0(B_108,C_109),C_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_2304])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3995,plain,(
    ! [A_145,B_146,C_147] : k3_xboole_0(A_145,k3_xboole_0(k4_xboole_0(B_146,C_147),C_147)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2336,c_2])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k3_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_148,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_139])).

tff(c_4480,plain,(
    ! [B_151,C_152] : k3_xboole_0(k4_xboole_0(B_151,C_152),C_152) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3995,c_148])).

tff(c_182,plain,(
    ! [A_1,C_38,B_39] :
      ( r1_xboole_0(A_1,C_38)
      | k3_xboole_0(A_1,k2_xboole_0(B_39,C_38)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_171])).

tff(c_4748,plain,(
    ! [B_154,B_155,C_156] : r1_xboole_0(k4_xboole_0(B_154,k2_xboole_0(B_155,C_156)),C_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_4480,c_182])).

tff(c_4804,plain,(
    ! [B_157,A_158] : r1_xboole_0(k4_xboole_0(B_157,A_158),A_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_1398,c_4748])).

tff(c_4865,plain,(
    ! [A_9,B_10] : r1_xboole_0(k3_xboole_0(A_9,B_10),k4_xboole_0(A_9,B_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4804])).

tff(c_28,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_70,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_88,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_88])).

tff(c_103,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_8510,plain,(
    ! [A_215,A_216] :
      ( r1_xboole_0(A_215,k3_xboole_0(A_216,'#skF_2'))
      | ~ r1_xboole_0(A_215,k4_xboole_0(A_216,'#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2248])).

tff(c_8582,plain,(
    ! [A_9] : r1_xboole_0(k3_xboole_0(A_9,'#skF_1'),k3_xboole_0(A_9,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_4865,c_8510])).

tff(c_26,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_9162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8582,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:27:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.48  
% 6.16/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.48  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.16/2.48  
% 6.16/2.48  %Foreground sorts:
% 6.16/2.48  
% 6.16/2.48  
% 6.16/2.48  %Background operators:
% 6.16/2.48  
% 6.16/2.48  
% 6.16/2.48  %Foreground operators:
% 6.16/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.16/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.16/2.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.16/2.48  tff('#skF_2', type, '#skF_2': $i).
% 6.16/2.48  tff('#skF_3', type, '#skF_3': $i).
% 6.16/2.48  tff('#skF_1', type, '#skF_1': $i).
% 6.16/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.16/2.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.16/2.48  
% 6.16/2.50  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.16/2.50  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.16/2.50  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.16/2.50  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.16/2.50  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 6.16/2.50  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.16/2.50  tff(f_59, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 6.16/2.50  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.16/2.50  tff(f_64, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 6.16/2.50  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.16/2.50  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.16/2.50  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.16/2.50  tff(c_121, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.16/2.50  tff(c_142, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_121])).
% 6.16/2.50  tff(c_150, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_142])).
% 6.16/2.50  tff(c_155, plain, (![A_36]: (k4_xboole_0(A_36, k1_xboole_0)=k3_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_150, c_14])).
% 6.16/2.50  tff(c_167, plain, (![A_36]: (k3_xboole_0(A_36, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_155])).
% 6.16/2.50  tff(c_149, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_142])).
% 6.16/2.50  tff(c_689, plain, (![A_64, B_65, C_66]: (k2_xboole_0(k4_xboole_0(A_64, B_65), k3_xboole_0(A_64, C_66))=k4_xboole_0(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.16/2.50  tff(c_736, plain, (![A_6, C_66]: (k4_xboole_0(A_6, k4_xboole_0(A_6, C_66))=k2_xboole_0(k1_xboole_0, k3_xboole_0(A_6, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_149, c_689])).
% 6.16/2.50  tff(c_1339, plain, (![A_81, C_82]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(A_81, C_82))=k3_xboole_0(A_81, C_82))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_736])).
% 6.16/2.50  tff(c_1376, plain, (![A_36]: (k3_xboole_0(A_36, A_36)=k2_xboole_0(k1_xboole_0, A_36))), inference(superposition, [status(thm), theory('equality')], [c_167, c_1339])).
% 6.16/2.50  tff(c_1398, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_1376])).
% 6.16/2.50  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.16/2.50  tff(c_45, plain, (![A_22, B_23]: (k2_xboole_0(A_22, k3_xboole_0(A_22, B_23))=A_22)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.16/2.50  tff(c_54, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_45])).
% 6.16/2.50  tff(c_171, plain, (![A_37, C_38, B_39]: (r1_xboole_0(A_37, C_38) | ~r1_xboole_0(A_37, k2_xboole_0(B_39, C_38)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.16/2.50  tff(c_294, plain, (![A_45, A_46]: (r1_xboole_0(A_45, k1_xboole_0) | ~r1_xboole_0(A_45, A_46))), inference(superposition, [status(thm), theory('equality')], [c_54, c_171])).
% 6.16/2.50  tff(c_310, plain, (![A_47, B_48]: (r1_xboole_0(A_47, k1_xboole_0) | k3_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_294])).
% 6.16/2.50  tff(c_319, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_310])).
% 6.16/2.50  tff(c_22, plain, (![A_17, C_19, B_18]: (r1_xboole_0(A_17, C_19) | ~r1_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.16/2.50  tff(c_2248, plain, (![A_103, A_104, C_105, B_106]: (r1_xboole_0(A_103, k3_xboole_0(A_104, C_105)) | ~r1_xboole_0(A_103, k4_xboole_0(A_104, k4_xboole_0(B_106, C_105))))), inference(superposition, [status(thm), theory('equality')], [c_689, c_22])).
% 6.16/2.50  tff(c_2304, plain, (![A_103, B_106, C_105]: (r1_xboole_0(A_103, k3_xboole_0(k4_xboole_0(B_106, C_105), C_105)) | ~r1_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_149, c_2248])).
% 6.16/2.50  tff(c_2336, plain, (![A_107, B_108, C_109]: (r1_xboole_0(A_107, k3_xboole_0(k4_xboole_0(B_108, C_109), C_109)))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_2304])).
% 6.16/2.50  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.16/2.50  tff(c_3995, plain, (![A_145, B_146, C_147]: (k3_xboole_0(A_145, k3_xboole_0(k4_xboole_0(B_146, C_147), C_147))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2336, c_2])).
% 6.16/2.50  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.16/2.50  tff(c_139, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k3_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 6.16/2.50  tff(c_148, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_139])).
% 6.16/2.50  tff(c_4480, plain, (![B_151, C_152]: (k3_xboole_0(k4_xboole_0(B_151, C_152), C_152)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3995, c_148])).
% 6.16/2.50  tff(c_182, plain, (![A_1, C_38, B_39]: (r1_xboole_0(A_1, C_38) | k3_xboole_0(A_1, k2_xboole_0(B_39, C_38))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_171])).
% 6.16/2.50  tff(c_4748, plain, (![B_154, B_155, C_156]: (r1_xboole_0(k4_xboole_0(B_154, k2_xboole_0(B_155, C_156)), C_156))), inference(superposition, [status(thm), theory('equality')], [c_4480, c_182])).
% 6.16/2.50  tff(c_4804, plain, (![B_157, A_158]: (r1_xboole_0(k4_xboole_0(B_157, A_158), A_158))), inference(superposition, [status(thm), theory('equality')], [c_1398, c_4748])).
% 6.16/2.50  tff(c_4865, plain, (![A_9, B_10]: (r1_xboole_0(k3_xboole_0(A_9, B_10), k4_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4804])).
% 6.16/2.50  tff(c_28, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.16/2.50  tff(c_66, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.16/2.50  tff(c_70, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_66])).
% 6.16/2.50  tff(c_88, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.16/2.50  tff(c_97, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_88])).
% 6.16/2.50  tff(c_103, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_97])).
% 6.16/2.50  tff(c_8510, plain, (![A_215, A_216]: (r1_xboole_0(A_215, k3_xboole_0(A_216, '#skF_2')) | ~r1_xboole_0(A_215, k4_xboole_0(A_216, '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_103, c_2248])).
% 6.16/2.50  tff(c_8582, plain, (![A_9]: (r1_xboole_0(k3_xboole_0(A_9, '#skF_1'), k3_xboole_0(A_9, '#skF_2')))), inference(resolution, [status(thm)], [c_4865, c_8510])).
% 6.16/2.50  tff(c_26, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.16/2.50  tff(c_9162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8582, c_26])).
% 6.16/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.50  
% 6.16/2.50  Inference rules
% 6.16/2.50  ----------------------
% 6.16/2.50  #Ref     : 0
% 6.16/2.50  #Sup     : 2235
% 6.16/2.50  #Fact    : 0
% 6.16/2.50  #Define  : 0
% 6.16/2.50  #Split   : 0
% 6.16/2.50  #Chain   : 0
% 6.16/2.50  #Close   : 0
% 6.16/2.50  
% 6.16/2.50  Ordering : KBO
% 6.16/2.50  
% 6.16/2.50  Simplification rules
% 6.16/2.50  ----------------------
% 6.16/2.50  #Subsume      : 40
% 6.16/2.50  #Demod        : 2387
% 6.16/2.50  #Tautology    : 1613
% 6.16/2.50  #SimpNegUnit  : 0
% 6.16/2.50  #BackRed      : 11
% 6.16/2.50  
% 6.16/2.50  #Partial instantiations: 0
% 6.16/2.50  #Strategies tried      : 1
% 6.16/2.50  
% 6.16/2.50  Timing (in seconds)
% 6.16/2.50  ----------------------
% 6.57/2.50  Preprocessing        : 0.32
% 6.57/2.50  Parsing              : 0.18
% 6.57/2.50  CNF conversion       : 0.02
% 6.57/2.50  Main loop            : 1.33
% 6.57/2.50  Inferencing          : 0.42
% 6.57/2.50  Reduction            : 0.59
% 6.57/2.50  Demodulation         : 0.48
% 6.57/2.50  BG Simplification    : 0.04
% 6.57/2.50  Subsumption          : 0.20
% 6.57/2.50  Abstraction          : 0.07
% 6.57/2.50  MUC search           : 0.00
% 6.57/2.50  Cooper               : 0.00
% 6.57/2.50  Total                : 1.68
% 6.57/2.50  Index Insertion      : 0.00
% 6.57/2.50  Index Deletion       : 0.00
% 6.57/2.50  Index Matching       : 0.00
% 6.57/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

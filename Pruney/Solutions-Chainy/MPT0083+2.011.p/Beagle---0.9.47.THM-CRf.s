%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:02 EST 2020

% Result     : Theorem 4.52s
% Output     : CNFRefutation 4.52s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 100 expanded)
%              Number of equality atoms :   34 (  71 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k4_xboole_0(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_160,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_163,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_160])).

tff(c_44,plain,(
    ! [B_19,A_20] : k3_xboole_0(B_19,A_20) = k3_xboole_0(A_20,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_20] : k3_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_226,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k3_xboole_0(A_36,B_37)) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_244,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_226])).

tff(c_259,plain,(
    ! [A_20] : k4_xboole_0(k1_xboole_0,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_244])).

tff(c_559,plain,(
    ! [A_50,B_51,C_52] : k2_xboole_0(k4_xboole_0(A_50,B_51),k3_xboole_0(A_50,C_52)) = k4_xboole_0(A_50,k4_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_625,plain,(
    ! [A_6,C_52] : k4_xboole_0(A_6,k4_xboole_0(k1_xboole_0,C_52)) = k2_xboole_0(A_6,k3_xboole_0(A_6,C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_559])).

tff(c_635,plain,(
    ! [A_6,C_52] : k2_xboole_0(A_6,k3_xboole_0(A_6,C_52)) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_259,c_625])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_124,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = k1_xboole_0
      | ~ r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_124])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_318,plain,(
    ! [B_39,A_40] : k4_xboole_0(B_39,k3_xboole_0(A_40,B_39)) = k4_xboole_0(B_39,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_226])).

tff(c_349,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_318])).

tff(c_370,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_349])).

tff(c_586,plain,(
    ! [C_52] : k4_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_52)) = k2_xboole_0('#skF_2',k3_xboole_0('#skF_2',C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_559])).

tff(c_1175,plain,(
    ! [C_70] : k4_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_70)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_586])).

tff(c_1183,plain,(
    ! [C_70] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_70)) = k4_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1175,c_14])).

tff(c_1225,plain,(
    ! [C_71] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_71)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_1183])).

tff(c_1280,plain,(
    ! [B_10] : k3_xboole_0('#skF_2',k3_xboole_0('#skF_1',B_10)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1225])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,C_16)
      | ~ r1_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2438,plain,(
    ! [A_93,A_94,C_95,B_96] :
      ( r1_xboole_0(A_93,k3_xboole_0(A_94,C_95))
      | ~ r1_xboole_0(A_93,k4_xboole_0(A_94,k4_xboole_0(B_96,C_95))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_20])).

tff(c_2521,plain,(
    ! [A_93,A_94,A_6] :
      ( r1_xboole_0(A_93,k3_xboole_0(A_94,A_6))
      | ~ r1_xboole_0(A_93,k4_xboole_0(A_94,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_2438])).

tff(c_2916,plain,(
    ! [A_104,A_105,A_106] :
      ( r1_xboole_0(A_104,k3_xboole_0(A_105,A_106))
      | ~ r1_xboole_0(A_104,A_105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2521])).

tff(c_4788,plain,(
    ! [A_136,B_137,A_138] :
      ( r1_xboole_0(A_136,k3_xboole_0(B_137,A_138))
      | ~ r1_xboole_0(A_136,A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2916])).

tff(c_24,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_27,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_4867,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4788,c_27])).

tff(c_4889,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_4867])).

tff(c_4893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_2,c_4889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:28:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.52/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.82  
% 4.52/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.82  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.52/1.82  
% 4.52/1.82  %Foreground sorts:
% 4.52/1.82  
% 4.52/1.82  
% 4.52/1.82  %Background operators:
% 4.52/1.82  
% 4.52/1.82  
% 4.52/1.82  %Foreground operators:
% 4.52/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.52/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.52/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.52/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.52/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.52/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.52/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.52/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.52/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.52/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.52/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.52/1.82  
% 4.52/1.83  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.52/1.83  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.52/1.83  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.52/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.52/1.83  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.52/1.83  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.52/1.83  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 4.52/1.83  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.52/1.83  tff(f_57, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.52/1.83  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.52/1.83  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.52/1.83  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.52/1.83  tff(c_145, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k4_xboole_0(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.52/1.83  tff(c_160, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 4.52/1.83  tff(c_163, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_160])).
% 4.52/1.83  tff(c_44, plain, (![B_19, A_20]: (k3_xboole_0(B_19, A_20)=k3_xboole_0(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.83  tff(c_60, plain, (![A_20]: (k3_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_44, c_8])).
% 4.52/1.83  tff(c_226, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k3_xboole_0(A_36, B_37))=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.52/1.83  tff(c_244, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_20))), inference(superposition, [status(thm), theory('equality')], [c_60, c_226])).
% 4.52/1.83  tff(c_259, plain, (![A_20]: (k4_xboole_0(k1_xboole_0, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_244])).
% 4.52/1.83  tff(c_559, plain, (![A_50, B_51, C_52]: (k2_xboole_0(k4_xboole_0(A_50, B_51), k3_xboole_0(A_50, C_52))=k4_xboole_0(A_50, k4_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.52/1.83  tff(c_625, plain, (![A_6, C_52]: (k4_xboole_0(A_6, k4_xboole_0(k1_xboole_0, C_52))=k2_xboole_0(A_6, k3_xboole_0(A_6, C_52)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_559])).
% 4.52/1.83  tff(c_635, plain, (![A_6, C_52]: (k2_xboole_0(A_6, k3_xboole_0(A_6, C_52))=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_259, c_625])).
% 4.52/1.83  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.52/1.83  tff(c_124, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=k1_xboole_0 | ~r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.83  tff(c_128, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_124])).
% 4.52/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.52/1.83  tff(c_318, plain, (![B_39, A_40]: (k4_xboole_0(B_39, k3_xboole_0(A_40, B_39))=k4_xboole_0(B_39, A_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_226])).
% 4.52/1.83  tff(c_349, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_128, c_318])).
% 4.52/1.83  tff(c_370, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_349])).
% 4.52/1.83  tff(c_586, plain, (![C_52]: (k4_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_52))=k2_xboole_0('#skF_2', k3_xboole_0('#skF_2', C_52)))), inference(superposition, [status(thm), theory('equality')], [c_370, c_559])).
% 4.52/1.83  tff(c_1175, plain, (![C_70]: (k4_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_70))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_635, c_586])).
% 4.52/1.83  tff(c_1183, plain, (![C_70]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_70))=k4_xboole_0('#skF_2', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1175, c_14])).
% 4.52/1.83  tff(c_1225, plain, (![C_71]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_71))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_1183])).
% 4.52/1.83  tff(c_1280, plain, (![B_10]: (k3_xboole_0('#skF_2', k3_xboole_0('#skF_1', B_10))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_1225])).
% 4.52/1.83  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.52/1.83  tff(c_20, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, C_16) | ~r1_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.52/1.83  tff(c_2438, plain, (![A_93, A_94, C_95, B_96]: (r1_xboole_0(A_93, k3_xboole_0(A_94, C_95)) | ~r1_xboole_0(A_93, k4_xboole_0(A_94, k4_xboole_0(B_96, C_95))))), inference(superposition, [status(thm), theory('equality')], [c_559, c_20])).
% 4.52/1.83  tff(c_2521, plain, (![A_93, A_94, A_6]: (r1_xboole_0(A_93, k3_xboole_0(A_94, A_6)) | ~r1_xboole_0(A_93, k4_xboole_0(A_94, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_2438])).
% 4.52/1.83  tff(c_2916, plain, (![A_104, A_105, A_106]: (r1_xboole_0(A_104, k3_xboole_0(A_105, A_106)) | ~r1_xboole_0(A_104, A_105))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2521])).
% 4.52/1.83  tff(c_4788, plain, (![A_136, B_137, A_138]: (r1_xboole_0(A_136, k3_xboole_0(B_137, A_138)) | ~r1_xboole_0(A_136, A_138))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2916])).
% 4.52/1.83  tff(c_24, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.52/1.83  tff(c_27, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 4.52/1.83  tff(c_4867, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_4788, c_27])).
% 4.52/1.83  tff(c_4889, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_4867])).
% 4.52/1.83  tff(c_4893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1280, c_2, c_4889])).
% 4.52/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.52/1.83  
% 4.52/1.83  Inference rules
% 4.52/1.83  ----------------------
% 4.52/1.83  #Ref     : 0
% 4.52/1.83  #Sup     : 1203
% 4.52/1.83  #Fact    : 0
% 4.52/1.83  #Define  : 0
% 4.52/1.83  #Split   : 0
% 4.52/1.83  #Chain   : 0
% 4.52/1.83  #Close   : 0
% 4.52/1.83  
% 4.52/1.83  Ordering : KBO
% 4.52/1.83  
% 4.52/1.83  Simplification rules
% 4.52/1.83  ----------------------
% 4.52/1.83  #Subsume      : 47
% 4.52/1.83  #Demod        : 1154
% 4.52/1.83  #Tautology    : 898
% 4.52/1.83  #SimpNegUnit  : 0
% 4.52/1.83  #BackRed      : 0
% 4.52/1.83  
% 4.52/1.83  #Partial instantiations: 0
% 4.52/1.83  #Strategies tried      : 1
% 4.52/1.83  
% 4.52/1.83  Timing (in seconds)
% 4.52/1.83  ----------------------
% 4.52/1.84  Preprocessing        : 0.28
% 4.52/1.84  Parsing              : 0.16
% 4.52/1.84  CNF conversion       : 0.02
% 4.52/1.84  Main loop            : 0.79
% 4.52/1.84  Inferencing          : 0.24
% 4.52/1.84  Reduction            : 0.37
% 4.52/1.84  Demodulation         : 0.31
% 4.52/1.84  BG Simplification    : 0.03
% 4.52/1.84  Subsumption          : 0.11
% 4.52/1.84  Abstraction          : 0.04
% 4.52/1.84  MUC search           : 0.00
% 4.52/1.84  Cooper               : 0.00
% 4.52/1.84  Total                : 1.09
% 4.52/1.84  Index Insertion      : 0.00
% 4.52/1.84  Index Deletion       : 0.00
% 4.52/1.84  Index Matching       : 0.00
% 4.52/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------

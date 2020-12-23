%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:51 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :   51 (  92 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_610,plain,(
    ! [A_59,B_60,C_61] :
      ( r2_hidden('#skF_1'(A_59,B_60,C_61),A_59)
      | r2_hidden('#skF_2'(A_59,B_60,C_61),C_61)
      | k4_xboole_0(A_59,B_60) = C_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_663,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_2'(A_59,B_60,A_59),A_59)
      | k4_xboole_0(A_59,B_60) = A_59 ) ),
    inference(resolution,[status(thm)],[c_610,c_16])).

tff(c_675,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_2'(A_62,B_63,A_62),A_62)
      | k4_xboole_0(A_62,B_63) = A_62 ) ),
    inference(resolution,[status(thm)],[c_610,c_16])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k4_xboole_0(A_3,B_4))
      | r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [B_17,A_18] : k2_xboole_0(B_17,A_18) = k2_xboole_0(A_18,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_18] : k2_xboole_0(k1_xboole_0,A_18) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_22])).

tff(c_134,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_165,plain,(
    ! [A_27] : k4_xboole_0(k1_xboole_0,A_27) = k4_xboole_0(A_27,A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_134])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_447,plain,(
    ! [D_45,A_46] :
      ( r2_hidden(D_45,A_46)
      | ~ r2_hidden(D_45,k4_xboole_0(k1_xboole_0,A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_8])).

tff(c_455,plain,(
    ! [D_8,B_4] :
      ( r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4,c_447])).

tff(c_1216,plain,(
    ! [B_84,B_85] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_84,k1_xboole_0),B_85)
      | k4_xboole_0(k1_xboole_0,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_675,c_455])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1280,plain,(
    ! [B_88,B_89] :
      ( ~ r2_hidden('#skF_2'(k1_xboole_0,B_88,k1_xboole_0),B_89)
      | k4_xboole_0(k1_xboole_0,B_88) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1216,c_6])).

tff(c_1310,plain,(
    ! [B_60] : k4_xboole_0(k1_xboole_0,B_60) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_663,c_1280])).

tff(c_152,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k4_xboole_0(A_18,A_18) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_134])).

tff(c_1343,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_152])).

tff(c_204,plain,(
    ! [A_31,B_32] : k2_xboole_0(A_31,k2_xboole_0(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_12,B_13] : k4_xboole_0(k2_xboole_0(A_12,B_13),B_13) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_213,plain,(
    ! [A_31,B_32] : k4_xboole_0(k2_xboole_0(A_31,B_32),k2_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,k2_xboole_0(A_31,B_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_26])).

tff(c_1416,plain,(
    ! [A_92,B_93] : k4_xboole_0(A_92,k2_xboole_0(A_92,B_93)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1343,c_213])).

tff(c_1465,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k2_xboole_0(B_2,A_1)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1416])).

tff(c_30,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_1489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1465,c_31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.53  
% 3.16/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.53  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.30/1.53  
% 3.30/1.53  %Foreground sorts:
% 3.30/1.53  
% 3.30/1.53  
% 3.30/1.53  %Background operators:
% 3.30/1.53  
% 3.30/1.53  
% 3.30/1.53  %Foreground operators:
% 3.30/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.30/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.30/1.53  
% 3.30/1.54  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.30/1.54  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.30/1.54  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.30/1.54  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.30/1.54  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 3.30/1.54  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.30/1.54  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.30/1.54  tff(c_610, plain, (![A_59, B_60, C_61]: (r2_hidden('#skF_1'(A_59, B_60, C_61), A_59) | r2_hidden('#skF_2'(A_59, B_60, C_61), C_61) | k4_xboole_0(A_59, B_60)=C_61)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.54  tff(c_16, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.54  tff(c_663, plain, (![A_59, B_60]: (r2_hidden('#skF_2'(A_59, B_60, A_59), A_59) | k4_xboole_0(A_59, B_60)=A_59)), inference(resolution, [status(thm)], [c_610, c_16])).
% 3.30/1.54  tff(c_675, plain, (![A_62, B_63]: (r2_hidden('#skF_2'(A_62, B_63, A_62), A_62) | k4_xboole_0(A_62, B_63)=A_62)), inference(resolution, [status(thm)], [c_610, c_16])).
% 3.30/1.54  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k4_xboole_0(A_3, B_4)) | r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.54  tff(c_41, plain, (![B_17, A_18]: (k2_xboole_0(B_17, A_18)=k2_xboole_0(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.30/1.54  tff(c_22, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.30/1.54  tff(c_57, plain, (![A_18]: (k2_xboole_0(k1_xboole_0, A_18)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_41, c_22])).
% 3.30/1.54  tff(c_134, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.30/1.54  tff(c_165, plain, (![A_27]: (k4_xboole_0(k1_xboole_0, A_27)=k4_xboole_0(A_27, A_27))), inference(superposition, [status(thm), theory('equality')], [c_57, c_134])).
% 3.30/1.54  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.54  tff(c_447, plain, (![D_45, A_46]: (r2_hidden(D_45, A_46) | ~r2_hidden(D_45, k4_xboole_0(k1_xboole_0, A_46)))), inference(superposition, [status(thm), theory('equality')], [c_165, c_8])).
% 3.30/1.54  tff(c_455, plain, (![D_8, B_4]: (r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_447])).
% 3.30/1.54  tff(c_1216, plain, (![B_84, B_85]: (r2_hidden('#skF_2'(k1_xboole_0, B_84, k1_xboole_0), B_85) | k4_xboole_0(k1_xboole_0, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_675, c_455])).
% 3.30/1.54  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.30/1.54  tff(c_1280, plain, (![B_88, B_89]: (~r2_hidden('#skF_2'(k1_xboole_0, B_88, k1_xboole_0), B_89) | k4_xboole_0(k1_xboole_0, B_88)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1216, c_6])).
% 3.30/1.54  tff(c_1310, plain, (![B_60]: (k4_xboole_0(k1_xboole_0, B_60)=k1_xboole_0)), inference(resolution, [status(thm)], [c_663, c_1280])).
% 3.30/1.54  tff(c_152, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k4_xboole_0(A_18, A_18))), inference(superposition, [status(thm), theory('equality')], [c_57, c_134])).
% 3.30/1.54  tff(c_1343, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_152])).
% 3.30/1.54  tff(c_204, plain, (![A_31, B_32]: (k2_xboole_0(A_31, k2_xboole_0(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.54  tff(c_26, plain, (![A_12, B_13]: (k4_xboole_0(k2_xboole_0(A_12, B_13), B_13)=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.30/1.54  tff(c_213, plain, (![A_31, B_32]: (k4_xboole_0(k2_xboole_0(A_31, B_32), k2_xboole_0(A_31, B_32))=k4_xboole_0(A_31, k2_xboole_0(A_31, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_204, c_26])).
% 3.30/1.54  tff(c_1416, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k2_xboole_0(A_92, B_93))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1343, c_213])).
% 3.30/1.54  tff(c_1465, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k2_xboole_0(B_2, A_1))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1416])).
% 3.30/1.54  tff(c_30, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.30/1.54  tff(c_31, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 3.30/1.54  tff(c_1489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1465, c_31])).
% 3.30/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.54  
% 3.30/1.54  Inference rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Ref     : 2
% 3.30/1.54  #Sup     : 341
% 3.30/1.54  #Fact    : 0
% 3.30/1.54  #Define  : 0
% 3.30/1.54  #Split   : 0
% 3.30/1.54  #Chain   : 0
% 3.30/1.54  #Close   : 0
% 3.30/1.54  
% 3.30/1.54  Ordering : KBO
% 3.30/1.54  
% 3.30/1.54  Simplification rules
% 3.30/1.54  ----------------------
% 3.30/1.54  #Subsume      : 72
% 3.30/1.54  #Demod        : 301
% 3.30/1.54  #Tautology    : 187
% 3.30/1.54  #SimpNegUnit  : 0
% 3.30/1.54  #BackRed      : 5
% 3.30/1.54  
% 3.30/1.54  #Partial instantiations: 0
% 3.30/1.54  #Strategies tried      : 1
% 3.30/1.54  
% 3.30/1.54  Timing (in seconds)
% 3.30/1.54  ----------------------
% 3.30/1.55  Preprocessing        : 0.29
% 3.30/1.55  Parsing              : 0.15
% 3.30/1.55  CNF conversion       : 0.02
% 3.30/1.55  Main loop            : 0.49
% 3.30/1.55  Inferencing          : 0.16
% 3.30/1.55  Reduction            : 0.20
% 3.30/1.55  Demodulation         : 0.17
% 3.30/1.55  BG Simplification    : 0.02
% 3.30/1.55  Subsumption          : 0.08
% 3.30/1.55  Abstraction          : 0.03
% 3.30/1.55  MUC search           : 0.00
% 3.30/1.55  Cooper               : 0.00
% 3.30/1.55  Total                : 0.80
% 3.30/1.55  Index Insertion      : 0.00
% 3.30/1.55  Index Deletion       : 0.00
% 3.30/1.55  Index Matching       : 0.00
% 3.30/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

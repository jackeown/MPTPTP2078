%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 5.55s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :   45 (  48 expanded)
%              Number of leaves         :   24 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 (  53 expanded)
%              Number of equality atoms :   24 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

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
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_32,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = k4_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_398,plain,(
    ! [D_55,B_56,A_57] :
      ( ~ r2_hidden(D_55,B_56)
      | ~ r2_hidden(D_55,k4_xboole_0(A_57,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5430,plain,(
    ! [A_187,A_188,B_189] :
      ( ~ r2_hidden('#skF_3'(A_187,k4_xboole_0(A_188,B_189)),B_189)
      | r1_xboole_0(A_187,k4_xboole_0(A_188,B_189)) ) ),
    inference(resolution,[status(thm)],[c_28,c_398])).

tff(c_5507,plain,(
    ! [A_190,A_191] : r1_xboole_0(A_190,k4_xboole_0(A_191,A_190)) ),
    inference(resolution,[status(thm)],[c_30,c_5430])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5574,plain,(
    ! [A_192,A_193] : k3_xboole_0(A_192,k4_xboole_0(A_193,A_192)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5507,c_22])).

tff(c_5606,plain,(
    ! [A_192,A_193] : k4_xboole_0(A_192,k4_xboole_0(A_193,A_192)) = k4_xboole_0(A_192,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5574,c_40])).

tff(c_5671,plain,(
    ! [A_192,A_193] : k4_xboole_0(A_192,k4_xboole_0(A_193,A_192)) = A_192 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5606])).

tff(c_255,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_21,B_22] : k4_xboole_0(k2_xboole_0(A_21,B_22),B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_265,plain,(
    ! [A_48,B_49] : k4_xboole_0(k2_xboole_0(A_48,B_49),k4_xboole_0(B_49,A_48)) = k4_xboole_0(A_48,k4_xboole_0(B_49,A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_38])).

tff(c_6198,plain,(
    ! [A_204,B_205] : k4_xboole_0(k2_xboole_0(A_204,B_205),k4_xboole_0(B_205,A_204)) = A_204 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5671,c_265])).

tff(c_6402,plain,(
    ! [A_23,B_24] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_23,B_24),A_23),k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_6198])).

tff(c_6462,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_6402])).

tff(c_42,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6462,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:03:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.55/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.22  
% 5.55/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.22  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 5.55/2.22  
% 5.55/2.22  %Foreground sorts:
% 5.55/2.22  
% 5.55/2.22  
% 5.55/2.22  %Background operators:
% 5.55/2.22  
% 5.55/2.22  
% 5.55/2.22  %Foreground operators:
% 5.55/2.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.55/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.55/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.55/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.55/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.55/2.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.55/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.55/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.55/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.55/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.55/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.55/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.55/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.55/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.55/2.22  
% 5.55/2.24  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.55/2.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.55/2.24  tff(f_69, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.55/2.24  tff(f_65, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.55/2.24  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.55/2.24  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.55/2.24  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.55/2.24  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.55/2.24  tff(f_67, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 5.55/2.24  tff(f_72, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.55/2.24  tff(c_32, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k3_xboole_0(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.55/2.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.55/2.24  tff(c_40, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k3_xboole_0(A_23, B_24))=k4_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.55/2.24  tff(c_36, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.55/2.24  tff(c_30, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.55/2.24  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.55/2.24  tff(c_398, plain, (![D_55, B_56, A_57]: (~r2_hidden(D_55, B_56) | ~r2_hidden(D_55, k4_xboole_0(A_57, B_56)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.55/2.24  tff(c_5430, plain, (![A_187, A_188, B_189]: (~r2_hidden('#skF_3'(A_187, k4_xboole_0(A_188, B_189)), B_189) | r1_xboole_0(A_187, k4_xboole_0(A_188, B_189)))), inference(resolution, [status(thm)], [c_28, c_398])).
% 5.55/2.24  tff(c_5507, plain, (![A_190, A_191]: (r1_xboole_0(A_190, k4_xboole_0(A_191, A_190)))), inference(resolution, [status(thm)], [c_30, c_5430])).
% 5.55/2.24  tff(c_22, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.55/2.24  tff(c_5574, plain, (![A_192, A_193]: (k3_xboole_0(A_192, k4_xboole_0(A_193, A_192))=k1_xboole_0)), inference(resolution, [status(thm)], [c_5507, c_22])).
% 5.55/2.24  tff(c_5606, plain, (![A_192, A_193]: (k4_xboole_0(A_192, k4_xboole_0(A_193, A_192))=k4_xboole_0(A_192, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5574, c_40])).
% 5.55/2.24  tff(c_5671, plain, (![A_192, A_193]: (k4_xboole_0(A_192, k4_xboole_0(A_193, A_192))=A_192)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5606])).
% 5.55/2.24  tff(c_255, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.55/2.24  tff(c_38, plain, (![A_21, B_22]: (k4_xboole_0(k2_xboole_0(A_21, B_22), B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.55/2.24  tff(c_265, plain, (![A_48, B_49]: (k4_xboole_0(k2_xboole_0(A_48, B_49), k4_xboole_0(B_49, A_48))=k4_xboole_0(A_48, k4_xboole_0(B_49, A_48)))), inference(superposition, [status(thm), theory('equality')], [c_255, c_38])).
% 5.55/2.24  tff(c_6198, plain, (![A_204, B_205]: (k4_xboole_0(k2_xboole_0(A_204, B_205), k4_xboole_0(B_205, A_204))=A_204)), inference(demodulation, [status(thm), theory('equality')], [c_5671, c_265])).
% 5.55/2.24  tff(c_6402, plain, (![A_23, B_24]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_23, B_24), A_23), k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_40, c_6198])).
% 5.55/2.24  tff(c_6462, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_6402])).
% 5.55/2.24  tff(c_42, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.55/2.24  tff(c_9304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6462, c_42])).
% 5.55/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.24  
% 5.55/2.24  Inference rules
% 5.55/2.24  ----------------------
% 5.55/2.24  #Ref     : 0
% 5.55/2.24  #Sup     : 2313
% 5.55/2.24  #Fact    : 0
% 5.55/2.24  #Define  : 0
% 5.55/2.24  #Split   : 0
% 5.55/2.24  #Chain   : 0
% 5.55/2.24  #Close   : 0
% 5.55/2.24  
% 5.55/2.24  Ordering : KBO
% 5.55/2.24  
% 5.55/2.24  Simplification rules
% 5.55/2.24  ----------------------
% 5.55/2.24  #Subsume      : 132
% 5.55/2.24  #Demod        : 2444
% 5.55/2.24  #Tautology    : 1685
% 5.55/2.24  #SimpNegUnit  : 0
% 5.55/2.24  #BackRed      : 5
% 5.55/2.24  
% 5.55/2.24  #Partial instantiations: 0
% 5.55/2.24  #Strategies tried      : 1
% 5.55/2.24  
% 5.55/2.24  Timing (in seconds)
% 5.55/2.24  ----------------------
% 5.55/2.24  Preprocessing        : 0.28
% 5.55/2.24  Parsing              : 0.15
% 5.55/2.24  CNF conversion       : 0.02
% 5.55/2.24  Main loop            : 1.17
% 5.55/2.24  Inferencing          : 0.35
% 5.55/2.24  Reduction            : 0.53
% 5.55/2.24  Demodulation         : 0.44
% 5.55/2.24  BG Simplification    : 0.04
% 5.55/2.24  Subsumption          : 0.19
% 5.55/2.24  Abstraction          : 0.06
% 5.55/2.24  MUC search           : 0.00
% 5.55/2.24  Cooper               : 0.00
% 5.55/2.24  Total                : 1.50
% 5.55/2.24  Index Insertion      : 0.00
% 5.55/2.24  Index Deletion       : 0.00
% 5.55/2.24  Index Matching       : 0.00
% 5.55/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

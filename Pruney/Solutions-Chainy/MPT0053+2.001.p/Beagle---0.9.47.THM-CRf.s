%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:50 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   42 (  51 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  73 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(c_42,plain,(
    ! [A_16,B_17] : k2_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden('#skF_3'(A_9,B_10,C_11),A_9)
      | r2_hidden('#skF_4'(A_9,B_10,C_11),C_11)
      | k4_xboole_0(A_9,B_10) = C_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1365,plain,(
    ! [A_133,B_134,C_135] :
      ( ~ r2_hidden('#skF_3'(A_133,B_134,C_135),B_134)
      | r2_hidden('#skF_4'(A_133,B_134,C_135),C_135)
      | k4_xboole_0(A_133,B_134) = C_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1382,plain,(
    ! [A_9,C_11] :
      ( r2_hidden('#skF_4'(A_9,A_9,C_11),C_11)
      | k4_xboole_0(A_9,A_9) = C_11 ) ),
    inference(resolution,[status(thm)],[c_38,c_1365])).

tff(c_1386,plain,(
    ! [A_136,C_137] :
      ( r2_hidden('#skF_4'(A_136,A_136,C_137),C_137)
      | k4_xboole_0(A_136,A_136) = C_137 ) ),
    inference(resolution,[status(thm)],[c_38,c_1365])).

tff(c_40,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_145,plain,(
    ! [D_28,B_29,A_30] :
      ( ~ r2_hidden(D_28,B_29)
      | r2_hidden(D_28,k2_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_157,plain,(
    ! [D_28,A_15] :
      ( ~ r2_hidden(D_28,k1_xboole_0)
      | r2_hidden(D_28,A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_145])).

tff(c_1474,plain,(
    ! [A_138,A_139] :
      ( r2_hidden('#skF_4'(A_138,A_138,k1_xboole_0),A_139)
      | k4_xboole_0(A_138,A_138) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1386,c_157])).

tff(c_44,plain,(
    ! [A_18,B_19,C_20] : k4_xboole_0(k4_xboole_0(A_18,B_19),C_20) = k4_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_219,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_267,plain,(
    ! [D_50,C_51,A_52,B_53] :
      ( ~ r2_hidden(D_50,C_51)
      | ~ r2_hidden(D_50,k4_xboole_0(A_52,k2_xboole_0(B_53,C_51))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_24])).

tff(c_271,plain,(
    ! [C_51,B_53,D_50,A_18,B_19] :
      ( ~ r2_hidden(D_50,C_51)
      | ~ r2_hidden(D_50,k4_xboole_0(A_18,k2_xboole_0(B_19,k2_xboole_0(B_53,C_51)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_267])).

tff(c_1562,plain,(
    ! [A_140,C_141] :
      ( ~ r2_hidden('#skF_4'(A_140,A_140,k1_xboole_0),C_141)
      | k4_xboole_0(A_140,A_140) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1474,c_271])).

tff(c_1640,plain,(
    ! [A_145] : k4_xboole_0(A_145,A_145) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1382,c_1562])).

tff(c_1708,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(B_19,k4_xboole_0(A_18,B_19))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1640,c_44])).

tff(c_1738,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k2_xboole_0(B_19,A_18)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1708])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_46,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_5','#skF_6')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,(
    k4_xboole_0('#skF_5',k2_xboole_0('#skF_6','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_46])).

tff(c_1844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1738,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:08:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.63  
% 3.40/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.63  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.40/1.63  
% 3.40/1.63  %Foreground sorts:
% 3.40/1.63  
% 3.40/1.63  
% 3.40/1.63  %Background operators:
% 3.40/1.63  
% 3.40/1.63  
% 3.40/1.63  %Foreground operators:
% 3.40/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.40/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.40/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.40/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.63  
% 3.40/1.64  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.40/1.64  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.40/1.64  tff(f_48, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.40/1.64  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.40/1.64  tff(f_52, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.40/1.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.40/1.64  tff(f_55, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.40/1.64  tff(c_42, plain, (![A_16, B_17]: (k2_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.40/1.64  tff(c_38, plain, (![A_9, B_10, C_11]: (r2_hidden('#skF_3'(A_9, B_10, C_11), A_9) | r2_hidden('#skF_4'(A_9, B_10, C_11), C_11) | k4_xboole_0(A_9, B_10)=C_11)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.64  tff(c_1365, plain, (![A_133, B_134, C_135]: (~r2_hidden('#skF_3'(A_133, B_134, C_135), B_134) | r2_hidden('#skF_4'(A_133, B_134, C_135), C_135) | k4_xboole_0(A_133, B_134)=C_135)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.64  tff(c_1382, plain, (![A_9, C_11]: (r2_hidden('#skF_4'(A_9, A_9, C_11), C_11) | k4_xboole_0(A_9, A_9)=C_11)), inference(resolution, [status(thm)], [c_38, c_1365])).
% 3.40/1.64  tff(c_1386, plain, (![A_136, C_137]: (r2_hidden('#skF_4'(A_136, A_136, C_137), C_137) | k4_xboole_0(A_136, A_136)=C_137)), inference(resolution, [status(thm)], [c_38, c_1365])).
% 3.40/1.64  tff(c_40, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.40/1.64  tff(c_145, plain, (![D_28, B_29, A_30]: (~r2_hidden(D_28, B_29) | r2_hidden(D_28, k2_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.40/1.64  tff(c_157, plain, (![D_28, A_15]: (~r2_hidden(D_28, k1_xboole_0) | r2_hidden(D_28, A_15))), inference(superposition, [status(thm), theory('equality')], [c_40, c_145])).
% 3.40/1.64  tff(c_1474, plain, (![A_138, A_139]: (r2_hidden('#skF_4'(A_138, A_138, k1_xboole_0), A_139) | k4_xboole_0(A_138, A_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1386, c_157])).
% 3.40/1.64  tff(c_44, plain, (![A_18, B_19, C_20]: (k4_xboole_0(k4_xboole_0(A_18, B_19), C_20)=k4_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.64  tff(c_219, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.64  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.40/1.64  tff(c_267, plain, (![D_50, C_51, A_52, B_53]: (~r2_hidden(D_50, C_51) | ~r2_hidden(D_50, k4_xboole_0(A_52, k2_xboole_0(B_53, C_51))))), inference(superposition, [status(thm), theory('equality')], [c_219, c_24])).
% 3.40/1.64  tff(c_271, plain, (![C_51, B_53, D_50, A_18, B_19]: (~r2_hidden(D_50, C_51) | ~r2_hidden(D_50, k4_xboole_0(A_18, k2_xboole_0(B_19, k2_xboole_0(B_53, C_51)))))), inference(superposition, [status(thm), theory('equality')], [c_44, c_267])).
% 3.40/1.64  tff(c_1562, plain, (![A_140, C_141]: (~r2_hidden('#skF_4'(A_140, A_140, k1_xboole_0), C_141) | k4_xboole_0(A_140, A_140)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1474, c_271])).
% 3.40/1.64  tff(c_1640, plain, (![A_145]: (k4_xboole_0(A_145, A_145)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1382, c_1562])).
% 3.40/1.64  tff(c_1708, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(B_19, k4_xboole_0(A_18, B_19)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1640, c_44])).
% 3.40/1.64  tff(c_1738, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k2_xboole_0(B_19, A_18))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1708])).
% 3.40/1.64  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.64  tff(c_46, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_5', '#skF_6'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.40/1.64  tff(c_47, plain, (k4_xboole_0('#skF_5', k2_xboole_0('#skF_6', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_46])).
% 3.40/1.64  tff(c_1844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1738, c_47])).
% 3.40/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.64  
% 3.40/1.64  Inference rules
% 3.40/1.64  ----------------------
% 3.40/1.64  #Ref     : 0
% 3.40/1.64  #Sup     : 434
% 3.40/1.64  #Fact    : 0
% 3.40/1.64  #Define  : 0
% 3.40/1.64  #Split   : 0
% 3.40/1.64  #Chain   : 0
% 3.40/1.64  #Close   : 0
% 3.40/1.64  
% 3.40/1.64  Ordering : KBO
% 3.40/1.64  
% 3.40/1.64  Simplification rules
% 3.40/1.64  ----------------------
% 3.40/1.64  #Subsume      : 129
% 3.40/1.64  #Demod        : 115
% 3.40/1.64  #Tautology    : 99
% 3.40/1.64  #SimpNegUnit  : 0
% 3.40/1.64  #BackRed      : 2
% 3.40/1.64  
% 3.40/1.64  #Partial instantiations: 0
% 3.40/1.64  #Strategies tried      : 1
% 3.40/1.64  
% 3.40/1.64  Timing (in seconds)
% 3.40/1.64  ----------------------
% 3.40/1.64  Preprocessing        : 0.29
% 3.40/1.64  Parsing              : 0.15
% 3.40/1.64  CNF conversion       : 0.02
% 3.40/1.64  Main loop            : 0.57
% 3.40/1.64  Inferencing          : 0.19
% 3.40/1.64  Reduction            : 0.20
% 3.40/1.64  Demodulation         : 0.16
% 3.40/1.64  BG Simplification    : 0.03
% 3.40/1.64  Subsumption          : 0.12
% 3.40/1.64  Abstraction          : 0.03
% 3.40/1.64  MUC search           : 0.00
% 3.40/1.64  Cooper               : 0.00
% 3.40/1.64  Total                : 0.89
% 3.40/1.64  Index Insertion      : 0.00
% 3.40/1.64  Index Deletion       : 0.00
% 3.40/1.64  Index Matching       : 0.00
% 3.40/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:30 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  86 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_65,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_73,plain,(
    ! [B_13] : k4_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_65])).

tff(c_36,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k3_xboole_0(A_16,B_17)) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_175,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_202,plain,(
    ! [B_13] : k4_xboole_0(B_13,k1_xboole_0) = k3_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_175])).

tff(c_138,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1393,plain,(
    ! [A_145,B_146,B_147] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_145,B_146),B_147),A_145)
      | r1_tarski(k4_xboole_0(A_145,B_146),B_147) ) ),
    inference(resolution,[status(thm)],[c_138,c_12])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1472,plain,(
    ! [A_148,B_149] : r1_tarski(k4_xboole_0(A_148,B_149),A_148) ),
    inference(resolution,[status(thm)],[c_1393,c_4])).

tff(c_1530,plain,(
    ! [B_150] : r1_tarski(k3_xboole_0(B_150,B_150),B_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_1472])).

tff(c_32,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_162,plain,(
    ! [B_57,A_58] :
      ( B_57 = A_58
      | ~ r1_tarski(B_57,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_169,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_162])).

tff(c_1539,plain,(
    ! [B_150] :
      ( k3_xboole_0(B_150,B_150) = B_150
      | k4_xboole_0(B_150,k3_xboole_0(B_150,B_150)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1530,c_169])).

tff(c_1565,plain,(
    ! [B_150] : k3_xboole_0(B_150,B_150) = B_150 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_36,c_1539])).

tff(c_1580,plain,(
    ! [B_13] : k4_xboole_0(B_13,k1_xboole_0) = B_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1565,c_202])).

tff(c_46,plain,(
    ! [A_26,B_27] : r1_tarski(k1_tarski(A_26),k2_tarski(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [A_26,B_27] : k4_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_199,plain,(
    ! [A_26,B_27] : k3_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k4_xboole_0(k1_tarski(A_26),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_175])).

tff(c_48,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),k2_tarski('#skF_4','#skF_5')) != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1179,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) != k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_48])).

tff(c_1683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1580,c_1179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:29 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.57  
% 3.46/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.57  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.46/1.57  
% 3.46/1.57  %Foreground sorts:
% 3.46/1.57  
% 3.46/1.57  
% 3.46/1.57  %Background operators:
% 3.46/1.57  
% 3.46/1.57  
% 3.46/1.57  %Foreground operators:
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.46/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.57  
% 3.46/1.58  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.46/1.58  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.46/1.58  tff(f_54, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 3.46/1.58  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.46/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.46/1.58  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.46/1.58  tff(f_64, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.46/1.58  tff(f_67, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.46/1.58  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.58  tff(c_65, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.58  tff(c_73, plain, (![B_13]: (k4_xboole_0(B_13, B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_65])).
% 3.46/1.58  tff(c_36, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k3_xboole_0(A_16, B_17))=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.46/1.58  tff(c_175, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.46/1.58  tff(c_202, plain, (![B_13]: (k4_xboole_0(B_13, k1_xboole_0)=k3_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_73, c_175])).
% 3.46/1.58  tff(c_138, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.58  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.46/1.58  tff(c_1393, plain, (![A_145, B_146, B_147]: (r2_hidden('#skF_1'(k4_xboole_0(A_145, B_146), B_147), A_145) | r1_tarski(k4_xboole_0(A_145, B_146), B_147))), inference(resolution, [status(thm)], [c_138, c_12])).
% 3.46/1.58  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.58  tff(c_1472, plain, (![A_148, B_149]: (r1_tarski(k4_xboole_0(A_148, B_149), A_148))), inference(resolution, [status(thm)], [c_1393, c_4])).
% 3.46/1.58  tff(c_1530, plain, (![B_150]: (r1_tarski(k3_xboole_0(B_150, B_150), B_150))), inference(superposition, [status(thm), theory('equality')], [c_202, c_1472])).
% 3.46/1.58  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.58  tff(c_162, plain, (![B_57, A_58]: (B_57=A_58 | ~r1_tarski(B_57, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.46/1.58  tff(c_169, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_162])).
% 3.46/1.58  tff(c_1539, plain, (![B_150]: (k3_xboole_0(B_150, B_150)=B_150 | k4_xboole_0(B_150, k3_xboole_0(B_150, B_150))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1530, c_169])).
% 3.46/1.58  tff(c_1565, plain, (![B_150]: (k3_xboole_0(B_150, B_150)=B_150)), inference(demodulation, [status(thm), theory('equality')], [c_73, c_36, c_1539])).
% 3.46/1.58  tff(c_1580, plain, (![B_13]: (k4_xboole_0(B_13, k1_xboole_0)=B_13)), inference(demodulation, [status(thm), theory('equality')], [c_1565, c_202])).
% 3.46/1.58  tff(c_46, plain, (![A_26, B_27]: (r1_tarski(k1_tarski(A_26), k2_tarski(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.58  tff(c_72, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_65])).
% 3.46/1.58  tff(c_199, plain, (![A_26, B_27]: (k3_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k4_xboole_0(k1_tarski(A_26), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_72, c_175])).
% 3.46/1.58  tff(c_48, plain, (k3_xboole_0(k1_tarski('#skF_4'), k2_tarski('#skF_4', '#skF_5'))!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.46/1.58  tff(c_1179, plain, (k4_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)!=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_199, c_48])).
% 3.46/1.58  tff(c_1683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1580, c_1179])).
% 3.46/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.58  
% 3.46/1.58  Inference rules
% 3.46/1.58  ----------------------
% 3.46/1.58  #Ref     : 0
% 3.46/1.58  #Sup     : 371
% 3.46/1.58  #Fact    : 0
% 3.46/1.58  #Define  : 0
% 3.46/1.58  #Split   : 0
% 3.46/1.58  #Chain   : 0
% 3.46/1.58  #Close   : 0
% 3.46/1.58  
% 3.46/1.58  Ordering : KBO
% 3.46/1.58  
% 3.46/1.58  Simplification rules
% 3.46/1.58  ----------------------
% 3.46/1.58  #Subsume      : 59
% 3.46/1.58  #Demod        : 199
% 3.46/1.58  #Tautology    : 182
% 3.46/1.58  #SimpNegUnit  : 0
% 3.46/1.58  #BackRed      : 14
% 3.46/1.58  
% 3.46/1.58  #Partial instantiations: 0
% 3.46/1.58  #Strategies tried      : 1
% 3.46/1.58  
% 3.46/1.58  Timing (in seconds)
% 3.46/1.58  ----------------------
% 3.46/1.58  Preprocessing        : 0.32
% 3.46/1.58  Parsing              : 0.16
% 3.46/1.58  CNF conversion       : 0.03
% 3.46/1.58  Main loop            : 0.50
% 3.46/1.58  Inferencing          : 0.19
% 3.46/1.58  Reduction            : 0.16
% 3.46/1.58  Demodulation         : 0.12
% 3.46/1.58  BG Simplification    : 0.02
% 3.46/1.58  Subsumption          : 0.09
% 3.46/1.58  Abstraction          : 0.03
% 3.46/1.58  MUC search           : 0.00
% 3.46/1.58  Cooper               : 0.00
% 3.46/1.58  Total                : 0.85
% 3.46/1.58  Index Insertion      : 0.00
% 3.46/1.59  Index Deletion       : 0.00
% 3.46/1.59  Index Matching       : 0.00
% 3.46/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

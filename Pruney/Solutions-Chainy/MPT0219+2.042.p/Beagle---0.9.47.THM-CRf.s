%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:55 EST 2020

% Result     : Theorem 8.05s
% Output     : CNFRefutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  72 expanded)
%              Number of equality atoms :   26 (  41 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_88,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_88,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_80,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_152,plain,(
    ! [A_59,B_60] : k1_enumset1(A_59,A_59,B_60) = k2_tarski(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_60,plain,(
    ! [E_33,A_27,C_29] : r2_hidden(E_33,k1_enumset1(A_27,E_33,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_170,plain,(
    ! [A_61,B_62] : r2_hidden(A_61,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_60])).

tff(c_173,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_170])).

tff(c_90,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k4_xboole_0(A_8,B_9))
      | r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_54,plain,(
    ! [A_25,B_26] : k5_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_935,plain,(
    ! [A_137,B_138,C_139] :
      ( r2_hidden(A_137,B_138)
      | ~ r2_hidden(A_137,C_139)
      | r2_hidden(A_137,k5_xboole_0(B_138,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17389,plain,(
    ! [A_18940,A_18941,B_18942] :
      ( r2_hidden(A_18940,A_18941)
      | ~ r2_hidden(A_18940,k4_xboole_0(B_18942,A_18941))
      | r2_hidden(A_18940,k2_xboole_0(A_18941,B_18942)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_935])).

tff(c_17489,plain,(
    ! [D_19060,B_19061,A_19062] :
      ( r2_hidden(D_19060,k2_xboole_0(B_19061,A_19062))
      | r2_hidden(D_19060,B_19061)
      | ~ r2_hidden(D_19060,A_19062) ) ),
    inference(resolution,[status(thm)],[c_10,c_17389])).

tff(c_17750,plain,(
    ! [D_19419] :
      ( r2_hidden(D_19419,k1_tarski('#skF_6'))
      | r2_hidden(D_19419,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_19419,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_17489])).

tff(c_17825,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_173,c_17750])).

tff(c_82,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1043,plain,(
    ! [E_141,C_142,B_143,A_144] :
      ( E_141 = C_142
      | E_141 = B_143
      | E_141 = A_144
      | ~ r2_hidden(E_141,k1_enumset1(A_144,B_143,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1569,plain,(
    ! [E_189,B_190,A_191] :
      ( E_189 = B_190
      | E_189 = A_191
      | E_189 = A_191
      | ~ r2_hidden(E_189,k2_tarski(A_191,B_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_1043])).

tff(c_1602,plain,(
    ! [E_189,A_34] :
      ( E_189 = A_34
      | E_189 = A_34
      | E_189 = A_34
      | ~ r2_hidden(E_189,k1_tarski(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1569])).

tff(c_17828,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_17825,c_1602])).

tff(c_17834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_88,c_88,c_17828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:26:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.05/2.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.05/2.77  
% 8.05/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.05/2.77  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_3 > #skF_1
% 8.05/2.77  
% 8.05/2.77  %Foreground sorts:
% 8.05/2.77  
% 8.05/2.77  
% 8.05/2.77  %Background operators:
% 8.05/2.77  
% 8.05/2.77  
% 8.05/2.77  %Foreground operators:
% 8.05/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.05/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.05/2.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.05/2.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.05/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.05/2.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.05/2.77  tff('#skF_7', type, '#skF_7': $i).
% 8.05/2.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.05/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.05/2.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.05/2.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.05/2.77  tff('#skF_6', type, '#skF_6': $i).
% 8.05/2.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.05/2.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.05/2.77  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 8.05/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.05/2.77  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 8.05/2.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.05/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.05/2.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.05/2.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.05/2.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.05/2.77  
% 8.26/2.78  tff(f_97, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 8.26/2.78  tff(f_86, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 8.26/2.78  tff(f_88, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.26/2.78  tff(f_84, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 8.26/2.78  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 8.26/2.78  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 8.26/2.78  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.26/2.78  tff(c_88, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.26/2.78  tff(c_80, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.26/2.78  tff(c_152, plain, (![A_59, B_60]: (k1_enumset1(A_59, A_59, B_60)=k2_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.26/2.78  tff(c_60, plain, (![E_33, A_27, C_29]: (r2_hidden(E_33, k1_enumset1(A_27, E_33, C_29)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.26/2.78  tff(c_170, plain, (![A_61, B_62]: (r2_hidden(A_61, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_152, c_60])).
% 8.26/2.78  tff(c_173, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_170])).
% 8.26/2.78  tff(c_90, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.26/2.78  tff(c_10, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, k4_xboole_0(A_8, B_9)) | r2_hidden(D_13, B_9) | ~r2_hidden(D_13, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.26/2.78  tff(c_54, plain, (![A_25, B_26]: (k5_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.26/2.78  tff(c_935, plain, (![A_137, B_138, C_139]: (r2_hidden(A_137, B_138) | ~r2_hidden(A_137, C_139) | r2_hidden(A_137, k5_xboole_0(B_138, C_139)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.26/2.78  tff(c_17389, plain, (![A_18940, A_18941, B_18942]: (r2_hidden(A_18940, A_18941) | ~r2_hidden(A_18940, k4_xboole_0(B_18942, A_18941)) | r2_hidden(A_18940, k2_xboole_0(A_18941, B_18942)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_935])).
% 8.26/2.78  tff(c_17489, plain, (![D_19060, B_19061, A_19062]: (r2_hidden(D_19060, k2_xboole_0(B_19061, A_19062)) | r2_hidden(D_19060, B_19061) | ~r2_hidden(D_19060, A_19062))), inference(resolution, [status(thm)], [c_10, c_17389])).
% 8.26/2.78  tff(c_17750, plain, (![D_19419]: (r2_hidden(D_19419, k1_tarski('#skF_6')) | r2_hidden(D_19419, k1_tarski('#skF_6')) | ~r2_hidden(D_19419, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_90, c_17489])).
% 8.26/2.78  tff(c_17825, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_173, c_17750])).
% 8.26/2.78  tff(c_82, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.26/2.78  tff(c_1043, plain, (![E_141, C_142, B_143, A_144]: (E_141=C_142 | E_141=B_143 | E_141=A_144 | ~r2_hidden(E_141, k1_enumset1(A_144, B_143, C_142)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.26/2.78  tff(c_1569, plain, (![E_189, B_190, A_191]: (E_189=B_190 | E_189=A_191 | E_189=A_191 | ~r2_hidden(E_189, k2_tarski(A_191, B_190)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_1043])).
% 8.26/2.78  tff(c_1602, plain, (![E_189, A_34]: (E_189=A_34 | E_189=A_34 | E_189=A_34 | ~r2_hidden(E_189, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1569])).
% 8.26/2.78  tff(c_17828, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_17825, c_1602])).
% 8.26/2.78  tff(c_17834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_88, c_88, c_17828])).
% 8.26/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.26/2.78  
% 8.26/2.78  Inference rules
% 8.26/2.78  ----------------------
% 8.26/2.78  #Ref     : 0
% 8.26/2.78  #Sup     : 3042
% 8.26/2.78  #Fact    : 20
% 8.26/2.78  #Define  : 0
% 8.26/2.78  #Split   : 0
% 8.26/2.78  #Chain   : 0
% 8.26/2.78  #Close   : 0
% 8.26/2.78  
% 8.26/2.78  Ordering : KBO
% 8.26/2.78  
% 8.26/2.78  Simplification rules
% 8.26/2.78  ----------------------
% 8.26/2.78  #Subsume      : 1155
% 8.26/2.78  #Demod        : 936
% 8.26/2.78  #Tautology    : 489
% 8.26/2.78  #SimpNegUnit  : 75
% 8.26/2.78  #BackRed      : 7
% 8.26/2.78  
% 8.26/2.78  #Partial instantiations: 8398
% 8.26/2.78  #Strategies tried      : 1
% 8.26/2.78  
% 8.26/2.78  Timing (in seconds)
% 8.26/2.78  ----------------------
% 8.26/2.78  Preprocessing        : 0.33
% 8.26/2.78  Parsing              : 0.17
% 8.26/2.78  CNF conversion       : 0.03
% 8.26/2.78  Main loop            : 1.69
% 8.26/2.78  Inferencing          : 0.74
% 8.26/2.78  Reduction            : 0.48
% 8.26/2.78  Demodulation         : 0.35
% 8.26/2.78  BG Simplification    : 0.08
% 8.26/2.78  Subsumption          : 0.29
% 8.26/2.78  Abstraction          : 0.11
% 8.26/2.78  MUC search           : 0.00
% 8.26/2.78  Cooper               : 0.00
% 8.26/2.78  Total                : 2.05
% 8.26/2.78  Index Insertion      : 0.00
% 8.26/2.78  Index Deletion       : 0.00
% 8.26/2.78  Index Matching       : 0.00
% 8.26/2.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------

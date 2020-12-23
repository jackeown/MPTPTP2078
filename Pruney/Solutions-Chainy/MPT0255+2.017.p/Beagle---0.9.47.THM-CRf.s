%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:41 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 147 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 ( 194 expanded)
%              Number of equality atoms :   21 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_79,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_44,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(k2_xboole_0(B_7,A_6))
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_111,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_115,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_16,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_149,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_173,plain,(
    ! [B_48,A_49] : k3_tarski(k2_tarski(B_48,A_49)) = k2_xboole_0(A_49,B_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_149])).

tff(c_42,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_196,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_42])).

tff(c_48,plain,(
    ! [B_35,A_36] :
      ( ~ v1_xboole_0(B_35)
      | B_35 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_51,plain,(
    ! [A_36] :
      ( k1_xboole_0 = A_36
      | ~ v1_xboole_0(A_36) ) ),
    inference(resolution,[status(thm)],[c_2,c_48])).

tff(c_122,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_115,c_51])).

tff(c_124,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_44])).

tff(c_214,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_124])).

tff(c_250,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_10])).

tff(c_254,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_250])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(B_10)
      | B_10 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_123,plain,(
    ! [A_9] :
      ( A_9 = '#skF_6'
      | ~ v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_115,c_14])).

tff(c_261,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_254,c_123])).

tff(c_22,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_279,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_22])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_126,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_12])).

tff(c_410,plain,(
    ! [A_65,B_66,C_67] :
      ( ~ r1_xboole_0(A_65,B_66)
      | ~ r2_hidden(C_67,B_66)
      | ~ r2_hidden(C_67,A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_423,plain,(
    ! [C_72,A_73] :
      ( ~ r2_hidden(C_72,'#skF_6')
      | ~ r2_hidden(C_72,A_73) ) ),
    inference(resolution,[status(thm)],[c_126,c_410])).

tff(c_437,plain,(
    ! [A_73] : ~ r2_hidden('#skF_4',A_73) ),
    inference(resolution,[status(thm)],[c_279,c_423])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_437,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:00:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.32  
% 2.46/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.33  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.46/1.33  
% 2.46/1.33  %Foreground sorts:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Background operators:
% 2.46/1.33  
% 2.46/1.33  
% 2.46/1.33  %Foreground operators:
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.46/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.46/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.46/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.33  tff('#skF_5', type, '#skF_5': $i).
% 2.46/1.33  tff('#skF_6', type, '#skF_6': $i).
% 2.46/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.46/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.46/1.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.46/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.46/1.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.46/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.46/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.46/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.33  
% 2.46/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.46/1.34  tff(f_83, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.46/1.34  tff(f_50, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.46/1.34  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.46/1.34  tff(f_79, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.46/1.34  tff(f_60, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.46/1.34  tff(f_71, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.46/1.34  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.46/1.34  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.46/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.46/1.34  tff(c_44, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.46/1.34  tff(c_10, plain, (![B_7, A_6]: (~v1_xboole_0(k2_xboole_0(B_7, A_6)) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.46/1.34  tff(c_111, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_44, c_10])).
% 2.46/1.34  tff(c_115, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_111])).
% 2.46/1.34  tff(c_16, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.46/1.34  tff(c_149, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.34  tff(c_173, plain, (![B_48, A_49]: (k3_tarski(k2_tarski(B_48, A_49))=k2_xboole_0(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_16, c_149])).
% 2.46/1.34  tff(c_42, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.46/1.34  tff(c_196, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_173, c_42])).
% 2.46/1.34  tff(c_48, plain, (![B_35, A_36]: (~v1_xboole_0(B_35) | B_35=A_36 | ~v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.34  tff(c_51, plain, (![A_36]: (k1_xboole_0=A_36 | ~v1_xboole_0(A_36))), inference(resolution, [status(thm)], [c_2, c_48])).
% 2.46/1.34  tff(c_122, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_115, c_51])).
% 2.46/1.34  tff(c_124, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_44])).
% 2.46/1.34  tff(c_214, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_196, c_124])).
% 2.46/1.34  tff(c_250, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_214, c_10])).
% 2.46/1.34  tff(c_254, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_250])).
% 2.46/1.34  tff(c_14, plain, (![B_10, A_9]: (~v1_xboole_0(B_10) | B_10=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.46/1.34  tff(c_123, plain, (![A_9]: (A_9='#skF_6' | ~v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_115, c_14])).
% 2.46/1.34  tff(c_261, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_254, c_123])).
% 2.46/1.34  tff(c_22, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.46/1.34  tff(c_279, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_261, c_22])).
% 2.46/1.34  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.46/1.34  tff(c_126, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_12])).
% 2.46/1.34  tff(c_410, plain, (![A_65, B_66, C_67]: (~r1_xboole_0(A_65, B_66) | ~r2_hidden(C_67, B_66) | ~r2_hidden(C_67, A_65))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.46/1.34  tff(c_423, plain, (![C_72, A_73]: (~r2_hidden(C_72, '#skF_6') | ~r2_hidden(C_72, A_73))), inference(resolution, [status(thm)], [c_126, c_410])).
% 2.46/1.34  tff(c_437, plain, (![A_73]: (~r2_hidden('#skF_4', A_73))), inference(resolution, [status(thm)], [c_279, c_423])).
% 2.46/1.34  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_437, c_279])).
% 2.46/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.34  
% 2.46/1.34  Inference rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Ref     : 0
% 2.46/1.34  #Sup     : 100
% 2.46/1.34  #Fact    : 0
% 2.46/1.34  #Define  : 0
% 2.46/1.34  #Split   : 1
% 2.46/1.34  #Chain   : 0
% 2.46/1.34  #Close   : 0
% 2.46/1.34  
% 2.46/1.34  Ordering : KBO
% 2.46/1.34  
% 2.46/1.34  Simplification rules
% 2.46/1.34  ----------------------
% 2.46/1.34  #Subsume      : 9
% 2.46/1.34  #Demod        : 38
% 2.46/1.34  #Tautology    : 70
% 2.46/1.34  #SimpNegUnit  : 1
% 2.46/1.34  #BackRed      : 8
% 2.46/1.34  
% 2.46/1.34  #Partial instantiations: 0
% 2.46/1.34  #Strategies tried      : 1
% 2.46/1.34  
% 2.46/1.34  Timing (in seconds)
% 2.46/1.34  ----------------------
% 2.46/1.34  Preprocessing        : 0.31
% 2.46/1.34  Parsing              : 0.17
% 2.46/1.34  CNF conversion       : 0.02
% 2.46/1.34  Main loop            : 0.22
% 2.46/1.34  Inferencing          : 0.07
% 2.46/1.34  Reduction            : 0.08
% 2.46/1.34  Demodulation         : 0.06
% 2.46/1.34  BG Simplification    : 0.01
% 2.46/1.34  Subsumption          : 0.04
% 2.46/1.34  Abstraction          : 0.01
% 2.46/1.34  MUC search           : 0.00
% 2.46/1.34  Cooper               : 0.00
% 2.46/1.34  Total                : 0.57
% 2.46/1.34  Index Insertion      : 0.00
% 2.46/1.34  Index Deletion       : 0.00
% 2.46/1.34  Index Matching       : 0.00
% 2.46/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:40 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 127 expanded)
%              Number of leaves         :   31 (  57 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 ( 160 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_54,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_135,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(k2_xboole_0(B_51,A_52))
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_138,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_135])).

tff(c_140,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_138])).

tff(c_125,plain,(
    ! [B_48,A_49] :
      ( ~ v1_xboole_0(B_48)
      | B_48 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_128,plain,(
    ! [A_49] :
      ( k1_xboole_0 = A_49
      | ~ v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_146,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_140,c_128])).

tff(c_20,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_167,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_20])).

tff(c_16,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_166,plain,(
    ! [A_10] : k3_xboole_0(A_10,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_146,c_16])).

tff(c_368,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,k3_xboole_0(A_67,B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_371,plain,(
    ! [A_10,C_69] :
      ( ~ r1_xboole_0(A_10,'#skF_6')
      | ~ r2_hidden(C_69,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_368])).

tff(c_373,plain,(
    ! [C_69] : ~ r2_hidden(C_69,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_371])).

tff(c_26,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_148,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_212,plain,(
    ! [A_61,B_62] : k3_tarski(k2_tarski(A_61,B_62)) = k2_xboole_0(B_62,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_148])).

tff(c_52,plain,(
    ! [A_34,B_35] : k3_tarski(k2_tarski(A_34,B_35)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_235,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,A_64) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_52])).

tff(c_165,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_54])).

tff(c_253,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_165])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ v1_xboole_0(k2_xboole_0(B_9,A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_311,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_14])).

tff(c_319,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_311])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ v1_xboole_0(B_16)
      | B_16 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    ! [A_15] :
      ( A_15 = '#skF_6'
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_140,c_24])).

tff(c_327,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_319,c_147])).

tff(c_32,plain,(
    ! [D_24,B_20] : r2_hidden(D_24,k2_tarski(D_24,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_347,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_32])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_373,c_347])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.14/1.25  
% 2.14/1.25  %Foreground sorts:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Background operators:
% 2.14/1.25  
% 2.14/1.25  
% 2.14/1.25  %Foreground operators:
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.14/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.14/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.14/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.14/1.25  
% 2.14/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.14/1.26  tff(f_91, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.14/1.26  tff(f_52, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.14/1.26  tff(f_68, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.14/1.26  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.14/1.26  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.14/1.26  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.14/1.26  tff(f_70, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.14/1.26  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.14/1.26  tff(f_79, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.14/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.14/1.26  tff(c_54, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.14/1.26  tff(c_135, plain, (![B_51, A_52]: (~v1_xboole_0(k2_xboole_0(B_51, A_52)) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.26  tff(c_138, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_54, c_135])).
% 2.14/1.26  tff(c_140, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_138])).
% 2.14/1.26  tff(c_125, plain, (![B_48, A_49]: (~v1_xboole_0(B_48) | B_48=A_49 | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.26  tff(c_128, plain, (![A_49]: (k1_xboole_0=A_49 | ~v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_2, c_125])).
% 2.14/1.26  tff(c_146, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_140, c_128])).
% 2.14/1.26  tff(c_20, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.26  tff(c_167, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_20])).
% 2.14/1.26  tff(c_16, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.26  tff(c_166, plain, (![A_10]: (k3_xboole_0(A_10, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_146, c_16])).
% 2.14/1.26  tff(c_368, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, k3_xboole_0(A_67, B_68)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.26  tff(c_371, plain, (![A_10, C_69]: (~r1_xboole_0(A_10, '#skF_6') | ~r2_hidden(C_69, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_166, c_368])).
% 2.14/1.26  tff(c_373, plain, (![C_69]: (~r2_hidden(C_69, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_371])).
% 2.14/1.26  tff(c_26, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.26  tff(c_148, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.26  tff(c_212, plain, (![A_61, B_62]: (k3_tarski(k2_tarski(A_61, B_62))=k2_xboole_0(B_62, A_61))), inference(superposition, [status(thm), theory('equality')], [c_26, c_148])).
% 2.14/1.26  tff(c_52, plain, (![A_34, B_35]: (k3_tarski(k2_tarski(A_34, B_35))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.14/1.26  tff(c_235, plain, (![B_63, A_64]: (k2_xboole_0(B_63, A_64)=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_212, c_52])).
% 2.14/1.26  tff(c_165, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_54])).
% 2.14/1.26  tff(c_253, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_235, c_165])).
% 2.14/1.26  tff(c_14, plain, (![B_9, A_8]: (~v1_xboole_0(k2_xboole_0(B_9, A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.26  tff(c_311, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_14])).
% 2.14/1.26  tff(c_319, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_311])).
% 2.14/1.26  tff(c_24, plain, (![B_16, A_15]: (~v1_xboole_0(B_16) | B_16=A_15 | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.26  tff(c_147, plain, (![A_15]: (A_15='#skF_6' | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_140, c_24])).
% 2.14/1.26  tff(c_327, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_319, c_147])).
% 2.14/1.26  tff(c_32, plain, (![D_24, B_20]: (r2_hidden(D_24, k2_tarski(D_24, B_20)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.14/1.26  tff(c_347, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_327, c_32])).
% 2.14/1.26  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_373, c_347])).
% 2.14/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  Inference rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Ref     : 0
% 2.14/1.26  #Sup     : 81
% 2.14/1.26  #Fact    : 0
% 2.14/1.26  #Define  : 0
% 2.14/1.26  #Split   : 0
% 2.14/1.26  #Chain   : 0
% 2.14/1.26  #Close   : 0
% 2.14/1.26  
% 2.14/1.26  Ordering : KBO
% 2.14/1.26  
% 2.14/1.26  Simplification rules
% 2.14/1.26  ----------------------
% 2.14/1.26  #Subsume      : 1
% 2.14/1.26  #Demod        : 37
% 2.14/1.26  #Tautology    : 60
% 2.14/1.26  #SimpNegUnit  : 2
% 2.14/1.26  #BackRed      : 13
% 2.14/1.26  
% 2.14/1.26  #Partial instantiations: 0
% 2.14/1.26  #Strategies tried      : 1
% 2.14/1.26  
% 2.14/1.26  Timing (in seconds)
% 2.14/1.26  ----------------------
% 2.14/1.27  Preprocessing        : 0.31
% 2.14/1.27  Parsing              : 0.16
% 2.14/1.27  CNF conversion       : 0.02
% 2.14/1.27  Main loop            : 0.21
% 2.14/1.27  Inferencing          : 0.06
% 2.14/1.27  Reduction            : 0.08
% 2.14/1.27  Demodulation         : 0.06
% 2.14/1.27  BG Simplification    : 0.01
% 2.14/1.27  Subsumption          : 0.04
% 2.14/1.27  Abstraction          : 0.01
% 2.14/1.27  MUC search           : 0.00
% 2.14/1.27  Cooper               : 0.00
% 2.14/1.27  Total                : 0.55
% 2.14/1.27  Index Insertion      : 0.00
% 2.14/1.27  Index Deletion       : 0.00
% 2.14/1.27  Index Matching       : 0.00
% 2.14/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:59 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 123 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 203 expanded)
%              Number of equality atoms :   23 (  85 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_56,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_32,plain,(
    k1_ordinal1('#skF_2') = k1_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_tarski(A_16)) = k1_ordinal1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_112,plain,(
    ! [B_42,A_43] :
      ( k4_xboole_0(k2_xboole_0(B_42,k1_tarski(A_43)),k1_tarski(A_43)) = B_42
      | r2_hidden(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_130,plain,(
    ! [A_44] :
      ( k4_xboole_0(k1_ordinal1(A_44),k1_tarski(A_44)) = A_44
      | r2_hidden(A_44,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_112])).

tff(c_145,plain,
    ( k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_2')) = '#skF_2'
    | r2_hidden('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_130])).

tff(c_148,plain,(
    r2_hidden('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_28,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_151,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_28])).

tff(c_157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_158,plain,(
    k4_xboole_0(k1_ordinal1('#skF_1'),k1_tarski('#skF_2')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(A_13,B_14)
      | ~ r2_hidden(A_13,k4_xboole_0(B_14,k1_tarski(C_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_195,plain,(
    ! [A_13] :
      ( r2_hidden(A_13,k1_ordinal1('#skF_1'))
      | ~ r2_hidden(A_13,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_22])).

tff(c_127,plain,(
    ! [A_16] :
      ( k4_xboole_0(k1_ordinal1(A_16),k1_tarski(A_16)) = A_16
      | r2_hidden(A_16,A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_112])).

tff(c_160,plain,(
    ! [A_45,B_46,C_47] :
      ( r2_hidden(A_45,k4_xboole_0(B_46,k1_tarski(C_47)))
      | C_47 = A_45
      | ~ r2_hidden(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_462,plain,(
    ! [B_64,C_65,A_66] :
      ( ~ r1_tarski(k4_xboole_0(B_64,k1_tarski(C_65)),A_66)
      | C_65 = A_66
      | ~ r2_hidden(A_66,B_64) ) ),
    inference(resolution,[status(thm)],[c_160,c_28])).

tff(c_1089,plain,(
    ! [A_101,A_102] :
      ( ~ r1_tarski(A_101,A_102)
      | A_102 = A_101
      | ~ r2_hidden(A_102,k1_ordinal1(A_101))
      | r2_hidden(A_101,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_462])).

tff(c_1101,plain,(
    ! [A_13] :
      ( ~ r1_tarski('#skF_1',A_13)
      | A_13 = '#skF_1'
      | r2_hidden('#skF_1','#skF_1')
      | ~ r2_hidden(A_13,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_195,c_1089])).

tff(c_1111,plain,(
    r2_hidden('#skF_1','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1101])).

tff(c_1149,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1111,c_28])).

tff(c_1157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1149])).

tff(c_1159,plain,(
    ~ r2_hidden('#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_30,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [A_17] : r2_hidden(A_17,k1_ordinal1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r2_hidden(A_13,k4_xboole_0(B_14,k1_tarski(C_15)))
      | C_15 = A_13
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_215,plain,(
    ! [A_49] :
      ( r2_hidden(A_49,'#skF_2')
      | A_49 = '#skF_2'
      | ~ r2_hidden(A_49,k1_ordinal1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_18])).

tff(c_225,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_215])).

tff(c_233,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_225])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_240,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_39,plain,(
    ! [A_21] : r2_hidden(A_21,k1_ordinal1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    r2_hidden('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_39])).

tff(c_1212,plain,(
    ! [A_107,A_108] :
      ( r2_hidden(A_107,A_108)
      | A_108 = A_107
      | ~ r2_hidden(A_107,k1_ordinal1(A_108))
      | r2_hidden(A_108,A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_160])).

tff(c_1218,plain,
    ( r2_hidden('#skF_2','#skF_1')
    | '#skF_2' = '#skF_1'
    | r2_hidden('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1212])).

tff(c_1230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1159,c_30,c_240,c_1218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:43:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.19/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  
% 3.33/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.54  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 3.33/1.54  
% 3.33/1.54  %Foreground sorts:
% 3.33/1.54  
% 3.33/1.54  
% 3.33/1.54  %Background operators:
% 3.33/1.54  
% 3.33/1.54  
% 3.33/1.54  %Foreground operators:
% 3.33/1.54  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.33/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.33/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.33/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.33/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.33/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.33/1.54  
% 3.33/1.55  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.33/1.55  tff(f_68, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 3.33/1.55  tff(f_56, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 3.33/1.55  tff(f_47, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 3.33/1.55  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.33/1.55  tff(f_54, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 3.33/1.55  tff(f_58, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 3.33/1.55  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.33/1.55  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.33/1.55  tff(c_32, plain, (k1_ordinal1('#skF_2')=k1_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.33/1.55  tff(c_24, plain, (![A_16]: (k2_xboole_0(A_16, k1_tarski(A_16))=k1_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.33/1.55  tff(c_112, plain, (![B_42, A_43]: (k4_xboole_0(k2_xboole_0(B_42, k1_tarski(A_43)), k1_tarski(A_43))=B_42 | r2_hidden(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.33/1.55  tff(c_130, plain, (![A_44]: (k4_xboole_0(k1_ordinal1(A_44), k1_tarski(A_44))=A_44 | r2_hidden(A_44, A_44))), inference(superposition, [status(thm), theory('equality')], [c_24, c_112])).
% 3.33/1.55  tff(c_145, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_2'))='#skF_2' | r2_hidden('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_130])).
% 3.33/1.55  tff(c_148, plain, (r2_hidden('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_145])).
% 3.33/1.55  tff(c_28, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.33/1.55  tff(c_151, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_148, c_28])).
% 3.33/1.55  tff(c_157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_151])).
% 3.33/1.55  tff(c_158, plain, (k4_xboole_0(k1_ordinal1('#skF_1'), k1_tarski('#skF_2'))='#skF_2'), inference(splitRight, [status(thm)], [c_145])).
% 3.33/1.55  tff(c_22, plain, (![A_13, B_14, C_15]: (r2_hidden(A_13, B_14) | ~r2_hidden(A_13, k4_xboole_0(B_14, k1_tarski(C_15))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.55  tff(c_195, plain, (![A_13]: (r2_hidden(A_13, k1_ordinal1('#skF_1')) | ~r2_hidden(A_13, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_22])).
% 3.33/1.55  tff(c_127, plain, (![A_16]: (k4_xboole_0(k1_ordinal1(A_16), k1_tarski(A_16))=A_16 | r2_hidden(A_16, A_16))), inference(superposition, [status(thm), theory('equality')], [c_24, c_112])).
% 3.33/1.55  tff(c_160, plain, (![A_45, B_46, C_47]: (r2_hidden(A_45, k4_xboole_0(B_46, k1_tarski(C_47))) | C_47=A_45 | ~r2_hidden(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.55  tff(c_462, plain, (![B_64, C_65, A_66]: (~r1_tarski(k4_xboole_0(B_64, k1_tarski(C_65)), A_66) | C_65=A_66 | ~r2_hidden(A_66, B_64))), inference(resolution, [status(thm)], [c_160, c_28])).
% 3.33/1.55  tff(c_1089, plain, (![A_101, A_102]: (~r1_tarski(A_101, A_102) | A_102=A_101 | ~r2_hidden(A_102, k1_ordinal1(A_101)) | r2_hidden(A_101, A_101))), inference(superposition, [status(thm), theory('equality')], [c_127, c_462])).
% 3.33/1.55  tff(c_1101, plain, (![A_13]: (~r1_tarski('#skF_1', A_13) | A_13='#skF_1' | r2_hidden('#skF_1', '#skF_1') | ~r2_hidden(A_13, '#skF_2'))), inference(resolution, [status(thm)], [c_195, c_1089])).
% 3.33/1.55  tff(c_1111, plain, (r2_hidden('#skF_1', '#skF_1')), inference(splitLeft, [status(thm)], [c_1101])).
% 3.33/1.55  tff(c_1149, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1111, c_28])).
% 3.33/1.55  tff(c_1157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1149])).
% 3.33/1.55  tff(c_1159, plain, (~r2_hidden('#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_1101])).
% 3.33/1.55  tff(c_30, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.33/1.55  tff(c_26, plain, (![A_17]: (r2_hidden(A_17, k1_ordinal1(A_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.33/1.55  tff(c_18, plain, (![A_13, B_14, C_15]: (r2_hidden(A_13, k4_xboole_0(B_14, k1_tarski(C_15))) | C_15=A_13 | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.33/1.55  tff(c_215, plain, (![A_49]: (r2_hidden(A_49, '#skF_2') | A_49='#skF_2' | ~r2_hidden(A_49, k1_ordinal1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_158, c_18])).
% 3.33/1.55  tff(c_225, plain, (r2_hidden('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_26, c_215])).
% 3.33/1.55  tff(c_233, plain, (r2_hidden('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_225])).
% 3.33/1.55  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.33/1.55  tff(c_240, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_233, c_2])).
% 3.33/1.55  tff(c_39, plain, (![A_21]: (r2_hidden(A_21, k1_ordinal1(A_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.33/1.55  tff(c_42, plain, (r2_hidden('#skF_2', k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_32, c_39])).
% 3.33/1.55  tff(c_1212, plain, (![A_107, A_108]: (r2_hidden(A_107, A_108) | A_108=A_107 | ~r2_hidden(A_107, k1_ordinal1(A_108)) | r2_hidden(A_108, A_108))), inference(superposition, [status(thm), theory('equality')], [c_127, c_160])).
% 3.33/1.55  tff(c_1218, plain, (r2_hidden('#skF_2', '#skF_1') | '#skF_2'='#skF_1' | r2_hidden('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_1212])).
% 3.33/1.55  tff(c_1230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1159, c_30, c_240, c_1218])).
% 3.33/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.55  
% 3.33/1.55  Inference rules
% 3.33/1.55  ----------------------
% 3.33/1.55  #Ref     : 0
% 3.33/1.55  #Sup     : 259
% 3.33/1.55  #Fact    : 0
% 3.33/1.55  #Define  : 0
% 3.33/1.55  #Split   : 3
% 3.33/1.55  #Chain   : 0
% 3.33/1.55  #Close   : 0
% 3.33/1.56  
% 3.33/1.56  Ordering : KBO
% 3.33/1.56  
% 3.33/1.56  Simplification rules
% 3.33/1.56  ----------------------
% 3.33/1.56  #Subsume      : 92
% 3.33/1.56  #Demod        : 37
% 3.33/1.56  #Tautology    : 30
% 3.33/1.56  #SimpNegUnit  : 11
% 3.33/1.56  #BackRed      : 0
% 3.33/1.56  
% 3.33/1.56  #Partial instantiations: 0
% 3.33/1.56  #Strategies tried      : 1
% 3.33/1.56  
% 3.33/1.56  Timing (in seconds)
% 3.33/1.56  ----------------------
% 3.33/1.56  Preprocessing        : 0.29
% 3.33/1.56  Parsing              : 0.16
% 3.33/1.56  CNF conversion       : 0.02
% 3.33/1.56  Main loop            : 0.50
% 3.33/1.56  Inferencing          : 0.17
% 3.33/1.56  Reduction            : 0.14
% 3.33/1.56  Demodulation         : 0.10
% 3.33/1.56  BG Simplification    : 0.02
% 3.33/1.56  Subsumption          : 0.13
% 3.33/1.56  Abstraction          : 0.02
% 3.33/1.56  MUC search           : 0.00
% 3.33/1.56  Cooper               : 0.00
% 3.33/1.56  Total                : 0.82
% 3.33/1.56  Index Insertion      : 0.00
% 3.33/1.56  Index Deletion       : 0.00
% 3.33/1.56  Index Matching       : 0.00
% 3.33/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------

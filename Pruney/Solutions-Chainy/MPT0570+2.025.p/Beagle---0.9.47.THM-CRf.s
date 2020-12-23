%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:44 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 125 expanded)
%              Number of equality atoms :   18 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_104,plain,(
    ! [B_39,A_40] :
      ( r1_xboole_0(k2_relat_1(B_39),A_40)
      | k10_relat_1(B_39,A_40) != k1_xboole_0
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_12,C_14,B_13] :
      ( r1_xboole_0(A_12,C_14)
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_177,plain,(
    ! [A_45,A_46,B_47] :
      ( r1_xboole_0(A_45,A_46)
      | ~ r1_tarski(A_45,k2_relat_1(B_47))
      | k10_relat_1(B_47,A_46) != k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_179,plain,(
    ! [A_46] :
      ( r1_xboole_0('#skF_3',A_46)
      | k10_relat_1('#skF_4',A_46) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_187,plain,(
    ! [A_48] :
      ( r1_xboole_0('#skF_3',A_48)
      | k10_relat_1('#skF_4',A_48) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_179])).

tff(c_12,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = A_19
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_12,c_36])).

tff(c_58,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,k3_xboole_0(A_22,B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    ! [B_9,C_24] :
      ( ~ r1_xboole_0(B_9,B_9)
      | ~ r2_hidden(C_24,B_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_198,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_3')
      | k10_relat_1('#skF_4','#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_187,c_64])).

tff(c_204,plain,(
    ! [C_24] : ~ r2_hidden(C_24,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_198])).

tff(c_43,plain,(
    k3_xboole_0('#skF_3',k2_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_36])).

tff(c_61,plain,(
    ! [C_24] :
      ( ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_24,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_58])).

tff(c_72,plain,(
    ~ r1_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_86,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),k3_xboole_0(A_36,B_37))
      | r1_xboole_0(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,
    ( r2_hidden('#skF_1'('#skF_3',k2_relat_1('#skF_4')),'#skF_3')
    | r1_xboole_0('#skF_3',k2_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_86])).

tff(c_97,plain,(
    r2_hidden('#skF_1'('#skF_3',k2_relat_1('#skF_4')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_92])).

tff(c_206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_204,c_97])).

tff(c_209,plain,(
    ! [C_49] : ~ r2_hidden(C_49,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_213,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_209])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.93/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.93/1.22  
% 1.93/1.23  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 1.93/1.23  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.93/1.23  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 1.93/1.23  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.93/1.23  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.93/1.23  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.93/1.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.93/1.23  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.93/1.23  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.23  tff(c_22, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.93/1.23  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.93/1.23  tff(c_24, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.93/1.23  tff(c_104, plain, (![B_39, A_40]: (r1_xboole_0(k2_relat_1(B_39), A_40) | k10_relat_1(B_39, A_40)!=k1_xboole_0 | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.93/1.23  tff(c_16, plain, (![A_12, C_14, B_13]: (r1_xboole_0(A_12, C_14) | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.93/1.23  tff(c_177, plain, (![A_45, A_46, B_47]: (r1_xboole_0(A_45, A_46) | ~r1_tarski(A_45, k2_relat_1(B_47)) | k10_relat_1(B_47, A_46)!=k1_xboole_0 | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_104, c_16])).
% 1.93/1.23  tff(c_179, plain, (![A_46]: (r1_xboole_0('#skF_3', A_46) | k10_relat_1('#skF_4', A_46)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_177])).
% 1.93/1.23  tff(c_187, plain, (![A_48]: (r1_xboole_0('#skF_3', A_48) | k10_relat_1('#skF_4', A_48)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_179])).
% 1.93/1.23  tff(c_12, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.23  tff(c_36, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=A_19 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.23  tff(c_44, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_12, c_36])).
% 1.93/1.23  tff(c_58, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, k3_xboole_0(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.23  tff(c_64, plain, (![B_9, C_24]: (~r1_xboole_0(B_9, B_9) | ~r2_hidden(C_24, B_9))), inference(superposition, [status(thm), theory('equality')], [c_44, c_58])).
% 1.93/1.23  tff(c_198, plain, (![C_24]: (~r2_hidden(C_24, '#skF_3') | k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_187, c_64])).
% 1.93/1.23  tff(c_204, plain, (![C_24]: (~r2_hidden(C_24, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_198])).
% 1.93/1.23  tff(c_43, plain, (k3_xboole_0('#skF_3', k2_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_36])).
% 1.93/1.23  tff(c_61, plain, (![C_24]: (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4')) | ~r2_hidden(C_24, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_58])).
% 1.93/1.23  tff(c_72, plain, (~r1_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_61])).
% 1.93/1.23  tff(c_86, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), k3_xboole_0(A_36, B_37)) | r1_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.93/1.23  tff(c_92, plain, (r2_hidden('#skF_1'('#skF_3', k2_relat_1('#skF_4')), '#skF_3') | r1_xboole_0('#skF_3', k2_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_43, c_86])).
% 1.93/1.23  tff(c_97, plain, (r2_hidden('#skF_1'('#skF_3', k2_relat_1('#skF_4')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_72, c_92])).
% 1.93/1.23  tff(c_206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_204, c_97])).
% 1.93/1.23  tff(c_209, plain, (![C_49]: (~r2_hidden(C_49, '#skF_3'))), inference(splitRight, [status(thm)], [c_61])).
% 1.93/1.23  tff(c_213, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_209])).
% 1.93/1.23  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_213])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 43
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 2
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 6
% 1.93/1.23  #Demod        : 9
% 1.93/1.23  #Tautology    : 14
% 1.93/1.23  #SimpNegUnit  : 3
% 1.93/1.23  #BackRed      : 1
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 1.93/1.23  Preprocessing        : 0.30
% 1.93/1.23  Parsing              : 0.16
% 1.93/1.23  CNF conversion       : 0.02
% 1.93/1.23  Main loop            : 0.17
% 1.93/1.23  Inferencing          : 0.06
% 1.93/1.24  Reduction            : 0.05
% 1.93/1.24  Demodulation         : 0.04
% 1.93/1.24  BG Simplification    : 0.01
% 1.93/1.24  Subsumption          : 0.03
% 1.93/1.24  Abstraction          : 0.01
% 1.93/1.24  MUC search           : 0.00
% 1.93/1.24  Cooper               : 0.00
% 1.93/1.24  Total                : 0.50
% 1.93/1.24  Index Insertion      : 0.00
% 1.93/1.24  Index Deletion       : 0.00
% 1.93/1.24  Index Matching       : 0.00
% 1.93/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:22:31 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  87 expanded)
%              Number of equality atoms :   10 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ~ ( m1_setfam_1(B,u1_struct_0(A))
                & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_tops_2)).

tff(f_48,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    l1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    m1_setfam_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_20])).

tff(c_94,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,k3_tarski(B_29))
      | ~ m1_setfam_1(B_29,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_4')
      | ~ m1_setfam_1('#skF_4',A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_94])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [C_46,B_47,A_48] :
      ( r2_hidden(C_46,B_47)
      | ~ r2_hidden(C_46,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_186,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_1'(A_51),B_52)
      | ~ r1_tarski(A_51,B_52)
      | v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_4,c_168])).

tff(c_14,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_14])).

tff(c_71,plain,(
    ! [A_20,B_21] : ~ r2_hidden(A_20,k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    ! [A_10] : ~ r2_hidden(A_10,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_71])).

tff(c_204,plain,(
    ! [A_53] :
      ( ~ r1_tarski(A_53,'#skF_4')
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_186,c_74])).

tff(c_226,plain,(
    ! [A_54] :
      ( v1_xboole_0(A_54)
      | ~ m1_setfam_1('#skF_4',A_54) ) ),
    inference(resolution,[status(thm)],[c_100,c_204])).

tff(c_247,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_226])).

tff(c_26,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_250,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_247,c_26])).

tff(c_253,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_250])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.32  
% 1.89/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.89/1.32  
% 1.89/1.32  %Foreground sorts:
% 1.89/1.32  
% 1.89/1.32  
% 1.89/1.32  %Background operators:
% 1.89/1.32  
% 1.89/1.32  
% 1.89/1.32  %Foreground operators:
% 1.89/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.89/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.89/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.32  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.32  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.89/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.89/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.89/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.32  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.89/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.89/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.89/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.89/1.32  
% 2.19/1.33  tff(f_74, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~(m1_setfam_1(B, u1_struct_0(A)) & (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_tops_2)).
% 2.19/1.33  tff(f_48, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.19/1.33  tff(f_52, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.19/1.33  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.19/1.33  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.33  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.19/1.33  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.19/1.33  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.19/1.33  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.33  tff(c_34, plain, (l1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.33  tff(c_30, plain, (m1_setfam_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.33  tff(c_28, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.19/1.33  tff(c_20, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.33  tff(c_37, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_20])).
% 2.19/1.33  tff(c_94, plain, (![A_28, B_29]: (r1_tarski(A_28, k3_tarski(B_29)) | ~m1_setfam_1(B_29, A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.33  tff(c_100, plain, (![A_28]: (r1_tarski(A_28, '#skF_4') | ~m1_setfam_1('#skF_4', A_28))), inference(superposition, [status(thm), theory('equality')], [c_37, c_94])).
% 2.19/1.33  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.33  tff(c_168, plain, (![C_46, B_47, A_48]: (r2_hidden(C_46, B_47) | ~r2_hidden(C_46, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.19/1.33  tff(c_186, plain, (![A_51, B_52]: (r2_hidden('#skF_1'(A_51), B_52) | ~r1_tarski(A_51, B_52) | v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_4, c_168])).
% 2.19/1.33  tff(c_14, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.19/1.33  tff(c_39, plain, (![A_10]: (k2_zfmisc_1(A_10, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_14])).
% 2.19/1.33  tff(c_71, plain, (![A_20, B_21]: (~r2_hidden(A_20, k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.19/1.33  tff(c_74, plain, (![A_10]: (~r2_hidden(A_10, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_71])).
% 2.19/1.33  tff(c_204, plain, (![A_53]: (~r1_tarski(A_53, '#skF_4') | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_186, c_74])).
% 2.19/1.33  tff(c_226, plain, (![A_54]: (v1_xboole_0(A_54) | ~m1_setfam_1('#skF_4', A_54))), inference(resolution, [status(thm)], [c_100, c_204])).
% 2.19/1.33  tff(c_247, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_30, c_226])).
% 2.19/1.33  tff(c_26, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.33  tff(c_250, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_247, c_26])).
% 2.19/1.33  tff(c_253, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_250])).
% 2.19/1.33  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_253])).
% 2.19/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  Inference rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Ref     : 0
% 2.19/1.33  #Sup     : 45
% 2.19/1.33  #Fact    : 0
% 2.19/1.33  #Define  : 0
% 2.19/1.33  #Split   : 0
% 2.19/1.33  #Chain   : 0
% 2.19/1.33  #Close   : 0
% 2.19/1.33  
% 2.19/1.33  Ordering : KBO
% 2.19/1.33  
% 2.19/1.33  Simplification rules
% 2.19/1.33  ----------------------
% 2.19/1.33  #Subsume      : 2
% 2.19/1.33  #Demod        : 18
% 2.19/1.33  #Tautology    : 24
% 2.19/1.33  #SimpNegUnit  : 1
% 2.19/1.33  #BackRed      : 0
% 2.19/1.33  
% 2.19/1.33  #Partial instantiations: 0
% 2.19/1.33  #Strategies tried      : 1
% 2.19/1.33  
% 2.19/1.33  Timing (in seconds)
% 2.19/1.33  ----------------------
% 2.19/1.34  Preprocessing        : 0.34
% 2.19/1.34  Parsing              : 0.19
% 2.19/1.34  CNF conversion       : 0.02
% 2.19/1.34  Main loop            : 0.19
% 2.19/1.34  Inferencing          : 0.07
% 2.19/1.34  Reduction            : 0.06
% 2.19/1.34  Demodulation         : 0.05
% 2.19/1.34  BG Simplification    : 0.01
% 2.19/1.34  Subsumption          : 0.03
% 2.19/1.34  Abstraction          : 0.01
% 2.19/1.34  MUC search           : 0.00
% 2.19/1.34  Cooper               : 0.00
% 2.19/1.34  Total                : 0.57
% 2.19/1.34  Index Insertion      : 0.00
% 2.19/1.34  Index Deletion       : 0.00
% 2.19/1.34  Index Matching       : 0.00
% 2.19/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------

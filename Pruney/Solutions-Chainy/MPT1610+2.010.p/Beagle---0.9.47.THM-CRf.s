%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:30 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   25 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  55 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_61,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_59,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_18,c_59])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_16] : k9_setfam_1(A_16) = k1_zfmisc_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [A_18] : k2_yellow_1(k9_setfam_1(A_18)) = k3_yellow_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    ! [A_18] : k2_yellow_1(k1_zfmisc_1(A_18)) = k3_yellow_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_87,plain,(
    ! [A_37] :
      ( k3_yellow_0(k2_yellow_1(A_37)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,(
    ! [A_57] :
      ( k3_yellow_0(k3_yellow_1(A_57)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_57))
      | v1_xboole_0(k1_zfmisc_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_87])).

tff(c_153,plain,(
    ! [A_5] :
      ( k3_yellow_0(k3_yellow_1(A_5)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(k1_xboole_0,A_5) ) ),
    inference(resolution,[status(thm)],[c_8,c_149])).

tff(c_162,plain,(
    ! [A_60] :
      ( k3_yellow_0(k3_yellow_1(A_60)) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_60)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_153])).

tff(c_65,plain,(
    ! [C_28,A_29] :
      ( r2_hidden(C_28,k1_zfmisc_1(A_29))
      | ~ r1_tarski(C_28,A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_29,C_28] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_29))
      | ~ r1_tarski(C_28,A_29) ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_166,plain,(
    ! [C_61,A_62] :
      ( ~ r1_tarski(C_61,A_62)
      | k3_yellow_0(k3_yellow_1(A_62)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_162,c_69])).

tff(c_175,plain,(
    ! [A_10] : k3_yellow_0(k3_yellow_1(A_10)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_166])).

tff(c_32,plain,(
    k3_yellow_0(k3_yellow_1('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  
% 1.81/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.19  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.81/1.19  
% 1.81/1.19  %Foreground sorts:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Background operators:
% 1.81/1.19  
% 1.81/1.19  
% 1.81/1.19  %Foreground operators:
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.19  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.81/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.81/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.19  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.81/1.19  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.81/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.81/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.19  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.81/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.81/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.81/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.81/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.19  
% 1.81/1.20  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.81/1.20  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.81/1.20  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.81/1.20  tff(f_52, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.81/1.20  tff(f_61, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.81/1.20  tff(f_59, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.81/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.81/1.20  tff(f_64, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.81/1.20  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.81/1.20  tff(c_59, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.81/1.20  tff(c_63, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_18, c_59])).
% 1.81/1.20  tff(c_8, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.20  tff(c_26, plain, (![A_16]: (k9_setfam_1(A_16)=k1_zfmisc_1(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.20  tff(c_30, plain, (![A_18]: (k2_yellow_1(k9_setfam_1(A_18))=k3_yellow_1(A_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.81/1.20  tff(c_33, plain, (![A_18]: (k2_yellow_1(k1_zfmisc_1(A_18))=k3_yellow_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 1.81/1.20  tff(c_87, plain, (![A_37]: (k3_yellow_0(k2_yellow_1(A_37))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.81/1.20  tff(c_149, plain, (![A_57]: (k3_yellow_0(k3_yellow_1(A_57))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_57)) | v1_xboole_0(k1_zfmisc_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_33, c_87])).
% 1.81/1.20  tff(c_153, plain, (![A_5]: (k3_yellow_0(k3_yellow_1(A_5))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_8, c_149])).
% 1.81/1.20  tff(c_162, plain, (![A_60]: (k3_yellow_0(k3_yellow_1(A_60))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_60)))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_153])).
% 1.81/1.20  tff(c_65, plain, (![C_28, A_29]: (r2_hidden(C_28, k1_zfmisc_1(A_29)) | ~r1_tarski(C_28, A_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.20  tff(c_69, plain, (![A_29, C_28]: (~v1_xboole_0(k1_zfmisc_1(A_29)) | ~r1_tarski(C_28, A_29))), inference(resolution, [status(thm)], [c_65, c_2])).
% 1.81/1.20  tff(c_166, plain, (![C_61, A_62]: (~r1_tarski(C_61, A_62) | k3_yellow_0(k3_yellow_1(A_62))=k1_xboole_0)), inference(resolution, [status(thm)], [c_162, c_69])).
% 1.81/1.20  tff(c_175, plain, (![A_10]: (k3_yellow_0(k3_yellow_1(A_10))=k1_xboole_0)), inference(resolution, [status(thm)], [c_63, c_166])).
% 1.81/1.20  tff(c_32, plain, (k3_yellow_0(k3_yellow_1('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.81/1.20  tff(c_180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_32])).
% 1.81/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  Inference rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Ref     : 0
% 1.81/1.20  #Sup     : 30
% 1.81/1.20  #Fact    : 0
% 1.81/1.20  #Define  : 0
% 1.81/1.20  #Split   : 1
% 1.81/1.20  #Chain   : 0
% 1.81/1.20  #Close   : 0
% 1.81/1.20  
% 1.81/1.20  Ordering : KBO
% 1.81/1.20  
% 1.81/1.20  Simplification rules
% 1.81/1.20  ----------------------
% 1.81/1.20  #Subsume      : 3
% 1.81/1.20  #Demod        : 5
% 1.81/1.20  #Tautology    : 11
% 1.81/1.20  #SimpNegUnit  : 0
% 1.81/1.20  #BackRed      : 1
% 1.81/1.20  
% 1.81/1.20  #Partial instantiations: 0
% 1.81/1.20  #Strategies tried      : 1
% 1.81/1.20  
% 1.81/1.20  Timing (in seconds)
% 1.81/1.20  ----------------------
% 1.81/1.21  Preprocessing        : 0.29
% 1.81/1.21  Parsing              : 0.15
% 1.81/1.21  CNF conversion       : 0.02
% 1.81/1.21  Main loop            : 0.15
% 1.81/1.21  Inferencing          : 0.06
% 1.81/1.21  Reduction            : 0.04
% 1.81/1.21  Demodulation         : 0.03
% 1.81/1.21  BG Simplification    : 0.01
% 1.81/1.21  Subsumption          : 0.03
% 1.81/1.21  Abstraction          : 0.01
% 1.81/1.21  MUC search           : 0.00
% 1.81/1.21  Cooper               : 0.00
% 1.81/1.21  Total                : 0.47
% 1.81/1.21  Index Insertion      : 0.00
% 1.81/1.21  Index Deletion       : 0.00
% 1.81/1.21  Index Matching       : 0.00
% 1.81/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

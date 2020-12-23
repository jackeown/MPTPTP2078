%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:35 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  74 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => k1_tops_1(A,k1_struct_0(A)) = k1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k1_struct_0(A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_32,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_37,plain,(
    ! [A_24] :
      ( k1_struct_0(A_24) = k1_xboole_0
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_43,plain,(
    ! [A_27] :
      ( k1_struct_0(A_27) = k1_xboole_0
      | ~ l1_pre_topc(A_27) ) ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_47,plain,(
    k1_struct_0('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_43])).

tff(c_30,plain,(
    k1_tops_1('#skF_3',k1_struct_0('#skF_3')) != k1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_47,c_30])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_153,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k1_tops_1(A_58,B_59),B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_166,plain,(
    ! [A_60] :
      ( r1_tarski(k1_tops_1(A_60,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_20,c_153])).

tff(c_58,plain,(
    ! [A_29,B_30] :
      ( r2_hidden('#skF_2'(A_29,B_30),A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_29,B_30] :
      ( ~ v1_xboole_0(A_29)
      | r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_71,plain,(
    ! [B_35,A_36] :
      ( B_35 = A_36
      | ~ r1_tarski(B_35,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [B_30,A_29] :
      ( B_30 = A_29
      | ~ r1_tarski(B_30,A_29)
      | ~ v1_xboole_0(A_29) ) ),
    inference(resolution,[status(thm)],[c_62,c_71])).

tff(c_172,plain,(
    ! [A_60] :
      ( k1_tops_1(A_60,k1_xboole_0) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_166,c_76])).

tff(c_190,plain,(
    ! [A_62] :
      ( k1_tops_1(A_62,k1_xboole_0) = k1_xboole_0
      | ~ l1_pre_topc(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_172])).

tff(c_193,plain,(
    k1_tops_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_190])).

tff(c_197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:38:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.19  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.79/1.19  
% 1.79/1.19  %Foreground sorts:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Background operators:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Foreground operators:
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.79/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.79/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.19  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 1.79/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.79/1.19  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 1.79/1.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.79/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.19  
% 1.98/1.20  tff(f_73, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (k1_tops_1(A, k1_struct_0(A)) = k1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_tops_1)).
% 1.98/1.20  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 1.98/1.20  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (k1_struct_0(A) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_struct_0)).
% 1.98/1.20  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.20  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.98/1.20  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 1.98/1.20  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.98/1.20  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.98/1.20  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.98/1.20  tff(c_32, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.98/1.20  tff(c_26, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.98/1.20  tff(c_37, plain, (![A_24]: (k1_struct_0(A_24)=k1_xboole_0 | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.98/1.20  tff(c_43, plain, (![A_27]: (k1_struct_0(A_27)=k1_xboole_0 | ~l1_pre_topc(A_27))), inference(resolution, [status(thm)], [c_26, c_37])).
% 1.98/1.20  tff(c_47, plain, (k1_struct_0('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_43])).
% 1.98/1.20  tff(c_30, plain, (k1_tops_1('#skF_3', k1_struct_0('#skF_3'))!=k1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.98/1.20  tff(c_52, plain, (k1_tops_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47, c_47, c_30])).
% 1.98/1.20  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.20  tff(c_20, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.20  tff(c_153, plain, (![A_58, B_59]: (r1_tarski(k1_tops_1(A_58, B_59), B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.98/1.20  tff(c_166, plain, (![A_60]: (r1_tarski(k1_tops_1(A_60, k1_xboole_0), k1_xboole_0) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_20, c_153])).
% 1.98/1.20  tff(c_58, plain, (![A_29, B_30]: (r2_hidden('#skF_2'(A_29, B_30), A_29) | r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.20  tff(c_62, plain, (![A_29, B_30]: (~v1_xboole_0(A_29) | r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.98/1.20  tff(c_71, plain, (![B_35, A_36]: (B_35=A_36 | ~r1_tarski(B_35, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.20  tff(c_76, plain, (![B_30, A_29]: (B_30=A_29 | ~r1_tarski(B_30, A_29) | ~v1_xboole_0(A_29))), inference(resolution, [status(thm)], [c_62, c_71])).
% 1.98/1.20  tff(c_172, plain, (![A_60]: (k1_tops_1(A_60, k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_166, c_76])).
% 1.98/1.20  tff(c_190, plain, (![A_62]: (k1_tops_1(A_62, k1_xboole_0)=k1_xboole_0 | ~l1_pre_topc(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_172])).
% 1.98/1.20  tff(c_193, plain, (k1_tops_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_190])).
% 1.98/1.20  tff(c_197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_193])).
% 1.98/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.20  
% 1.98/1.20  Inference rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Ref     : 0
% 1.98/1.20  #Sup     : 34
% 1.98/1.20  #Fact    : 0
% 1.98/1.20  #Define  : 0
% 1.98/1.20  #Split   : 0
% 1.98/1.20  #Chain   : 0
% 1.98/1.20  #Close   : 0
% 1.98/1.20  
% 1.98/1.20  Ordering : KBO
% 1.98/1.20  
% 1.98/1.20  Simplification rules
% 1.98/1.20  ----------------------
% 1.98/1.20  #Subsume      : 0
% 1.98/1.20  #Demod        : 8
% 1.98/1.20  #Tautology    : 11
% 1.98/1.20  #SimpNegUnit  : 1
% 1.98/1.20  #BackRed      : 0
% 1.98/1.20  
% 1.98/1.20  #Partial instantiations: 0
% 1.98/1.20  #Strategies tried      : 1
% 1.98/1.20  
% 1.98/1.20  Timing (in seconds)
% 1.98/1.20  ----------------------
% 1.98/1.21  Preprocessing        : 0.27
% 1.98/1.21  Parsing              : 0.15
% 1.98/1.21  CNF conversion       : 0.02
% 1.98/1.21  Main loop            : 0.18
% 1.98/1.21  Inferencing          : 0.07
% 1.98/1.21  Reduction            : 0.04
% 1.98/1.21  Demodulation         : 0.03
% 1.98/1.21  BG Simplification    : 0.01
% 1.98/1.21  Subsumption          : 0.04
% 1.98/1.21  Abstraction          : 0.01
% 1.98/1.21  MUC search           : 0.00
% 1.98/1.21  Cooper               : 0.00
% 1.98/1.21  Total                : 0.48
% 1.98/1.21  Index Insertion      : 0.00
% 1.98/1.21  Index Deletion       : 0.00
% 1.98/1.21  Index Matching       : 0.00
% 1.98/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

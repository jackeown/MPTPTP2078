%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  53 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 137 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( m1_pre_topc(B,C)
              <=> k1_tsep_1(A,B,C) = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_16,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != k1_tsep_1('#skF_2','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_18,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( ~ r2_hidden('#skF_1'(A_23,B_24),B_24)
      | r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_28])).

tff(c_62,plain,(
    ! [B_40,C_41,A_42] :
      ( m1_pre_topc(B_40,C_41)
      | ~ r1_tarski(u1_struct_0(B_40),u1_struct_0(C_41))
      | ~ m1_pre_topc(C_41,A_42)
      | ~ m1_pre_topc(B_40,A_42)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    ! [B_46,A_47] :
      ( m1_pre_topc(B_46,B_46)
      | ~ m1_pre_topc(B_46,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_33,c_62])).

tff(c_78,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_76])).

tff(c_81,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_78])).

tff(c_10,plain,(
    ! [A_6,B_10,C_12] :
      ( k1_tsep_1(A_6,B_10,C_12) = g1_pre_topc(u1_struct_0(C_12),u1_pre_topc(C_12))
      | ~ m1_pre_topc(B_10,C_12)
      | ~ m1_pre_topc(C_12,A_6)
      | v2_struct_0(C_12)
      | ~ m1_pre_topc(B_10,A_6)
      | v2_struct_0(B_10)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [A_6] :
      ( k1_tsep_1(A_6,'#skF_3','#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_6)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_81,c_10])).

tff(c_95,plain,(
    ! [A_48] :
      ( k1_tsep_1(A_48,'#skF_3','#skF_3') = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_85])).

tff(c_99,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_105,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_2','#skF_3','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_99])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_16,c_105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:01:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.14  
% 1.82/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.14  %$ r2_hidden > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tsep_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > #skF_2 > #skF_3 > #skF_1
% 1.82/1.14  
% 1.82/1.14  %Foreground sorts:
% 1.82/1.14  
% 1.82/1.14  
% 1.82/1.14  %Background operators:
% 1.82/1.14  
% 1.82/1.14  
% 1.82/1.14  %Foreground operators:
% 1.82/1.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.82/1.14  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 1.82/1.14  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.14  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 1.82/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.82/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.82/1.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.82/1.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.82/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.14  
% 1.82/1.15  tff(f_85, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 1.82/1.15  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.82/1.15  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 1.82/1.15  tff(f_55, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) <=> (k1_tsep_1(A, B, C) = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tsep_1)).
% 1.82/1.15  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.15  tff(c_16, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!=k1_tsep_1('#skF_2', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.15  tff(c_24, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.15  tff(c_22, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.15  tff(c_18, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.15  tff(c_20, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.82/1.15  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.15  tff(c_28, plain, (![A_23, B_24]: (~r2_hidden('#skF_1'(A_23, B_24), B_24) | r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.82/1.15  tff(c_33, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_28])).
% 1.82/1.15  tff(c_62, plain, (![B_40, C_41, A_42]: (m1_pre_topc(B_40, C_41) | ~r1_tarski(u1_struct_0(B_40), u1_struct_0(C_41)) | ~m1_pre_topc(C_41, A_42) | ~m1_pre_topc(B_40, A_42) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.82/1.15  tff(c_76, plain, (![B_46, A_47]: (m1_pre_topc(B_46, B_46) | ~m1_pre_topc(B_46, A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(resolution, [status(thm)], [c_33, c_62])).
% 1.82/1.15  tff(c_78, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_18, c_76])).
% 1.82/1.15  tff(c_81, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_78])).
% 1.82/1.15  tff(c_10, plain, (![A_6, B_10, C_12]: (k1_tsep_1(A_6, B_10, C_12)=g1_pre_topc(u1_struct_0(C_12), u1_pre_topc(C_12)) | ~m1_pre_topc(B_10, C_12) | ~m1_pre_topc(C_12, A_6) | v2_struct_0(C_12) | ~m1_pre_topc(B_10, A_6) | v2_struct_0(B_10) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.82/1.15  tff(c_85, plain, (![A_6]: (k1_tsep_1(A_6, '#skF_3', '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_6) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(resolution, [status(thm)], [c_81, c_10])).
% 1.82/1.15  tff(c_95, plain, (![A_48]: (k1_tsep_1(A_48, '#skF_3', '#skF_3')=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')) | ~m1_pre_topc('#skF_3', A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_85])).
% 1.82/1.15  tff(c_99, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_95])).
% 1.82/1.15  tff(c_105, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_2', '#skF_3', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_99])).
% 1.82/1.15  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_16, c_105])).
% 1.82/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.15  
% 1.82/1.15  Inference rules
% 1.82/1.15  ----------------------
% 1.82/1.15  #Ref     : 0
% 1.82/1.15  #Sup     : 16
% 1.82/1.15  #Fact    : 0
% 1.82/1.15  #Define  : 0
% 1.82/1.15  #Split   : 1
% 1.82/1.15  #Chain   : 0
% 1.82/1.15  #Close   : 0
% 1.82/1.16  
% 1.82/1.16  Ordering : KBO
% 1.82/1.16  
% 1.82/1.16  Simplification rules
% 1.82/1.16  ----------------------
% 1.82/1.16  #Subsume      : 1
% 1.82/1.16  #Demod        : 7
% 1.82/1.16  #Tautology    : 3
% 1.82/1.16  #SimpNegUnit  : 4
% 1.82/1.16  #BackRed      : 0
% 1.82/1.16  
% 1.82/1.16  #Partial instantiations: 0
% 1.82/1.16  #Strategies tried      : 1
% 1.82/1.16  
% 1.82/1.16  Timing (in seconds)
% 1.82/1.16  ----------------------
% 1.93/1.16  Preprocessing        : 0.28
% 1.93/1.16  Parsing              : 0.16
% 1.93/1.16  CNF conversion       : 0.02
% 1.93/1.16  Main loop            : 0.14
% 1.93/1.16  Inferencing          : 0.06
% 1.93/1.16  Reduction            : 0.04
% 1.93/1.16  Demodulation         : 0.03
% 1.93/1.16  BG Simplification    : 0.01
% 1.93/1.16  Subsumption          : 0.03
% 1.93/1.16  Abstraction          : 0.01
% 1.93/1.16  MUC search           : 0.00
% 1.93/1.16  Cooper               : 0.00
% 1.93/1.16  Total                : 0.44
% 1.93/1.16  Index Insertion      : 0.00
% 1.93/1.16  Index Deletion       : 0.00
% 1.93/1.16  Index Matching       : 0.00
% 1.93/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

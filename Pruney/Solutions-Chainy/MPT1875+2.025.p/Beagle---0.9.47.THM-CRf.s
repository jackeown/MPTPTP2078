%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:49 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 108 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_27,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_10,plain,(
    ! [A_5] :
      ( v2_tex_2(u1_struct_0(A_5),A_5)
      | ~ v1_tdlat_3(A_5)
      | ~ m1_subset_1(u1_struct_0(A_5),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_31,plain,(
    ! [A_5] :
      ( v2_tex_2(u1_struct_0(A_5),A_5)
      | ~ v1_tdlat_3(A_5)
      | ~ l1_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_10])).

tff(c_16,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_43])).

tff(c_63,plain,(
    ! [C_25,A_26,B_27] :
      ( v2_tex_2(C_25,A_26)
      | ~ v2_tex_2(B_27,A_26)
      | ~ r1_tarski(C_25,B_27)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_70,plain,(
    ! [A_28] :
      ( v2_tex_2('#skF_2',A_28)
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_28)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_77,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27,c_70])).

tff(c_81,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_77])).

tff(c_82,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_81])).

tff(c_85,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_31,c_82])).

tff(c_88,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_85])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:41:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.21  %$ v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.82/1.21  
% 1.82/1.21  %Foreground sorts:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Background operators:
% 1.82/1.21  
% 1.82/1.21  
% 1.82/1.21  %Foreground operators:
% 1.82/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.82/1.21  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.82/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.21  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.82/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.82/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.82/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.82/1.21  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.82/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.21  
% 1.94/1.22  tff(f_76, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 1.94/1.22  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.94/1.22  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.94/1.22  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 1.94/1.22  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.94/1.22  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 1.94/1.22  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.22  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.22  tff(c_22, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.22  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.94/1.22  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.22  tff(c_27, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.94/1.22  tff(c_10, plain, (![A_5]: (v2_tex_2(u1_struct_0(A_5), A_5) | ~v1_tdlat_3(A_5) | ~m1_subset_1(u1_struct_0(A_5), k1_zfmisc_1(u1_struct_0(A_5))) | ~l1_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.94/1.22  tff(c_31, plain, (![A_5]: (v2_tex_2(u1_struct_0(A_5), A_5) | ~v1_tdlat_3(A_5) | ~l1_pre_topc(A_5) | v2_struct_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_10])).
% 1.94/1.22  tff(c_16, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.22  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.94/1.22  tff(c_43, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.94/1.22  tff(c_54, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_18, c_43])).
% 1.94/1.22  tff(c_63, plain, (![C_25, A_26, B_27]: (v2_tex_2(C_25, A_26) | ~v2_tex_2(B_27, A_26) | ~r1_tarski(C_25, B_27) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.94/1.22  tff(c_70, plain, (![A_28]: (v2_tex_2('#skF_2', A_28) | ~v2_tex_2(u1_struct_0('#skF_1'), A_28) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_54, c_63])).
% 1.94/1.22  tff(c_77, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27, c_70])).
% 1.94/1.22  tff(c_81, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_77])).
% 1.94/1.22  tff(c_82, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_16, c_81])).
% 1.94/1.22  tff(c_85, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_31, c_82])).
% 1.94/1.22  tff(c_88, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_85])).
% 1.94/1.22  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_88])).
% 1.94/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  Inference rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Ref     : 0
% 1.94/1.22  #Sup     : 11
% 1.94/1.22  #Fact    : 0
% 1.94/1.22  #Define  : 0
% 1.94/1.22  #Split   : 0
% 1.94/1.22  #Chain   : 0
% 1.94/1.22  #Close   : 0
% 1.94/1.22  
% 1.94/1.22  Ordering : KBO
% 1.94/1.22  
% 1.94/1.22  Simplification rules
% 1.94/1.22  ----------------------
% 1.94/1.22  #Subsume      : 0
% 1.94/1.22  #Demod        : 7
% 1.94/1.22  #Tautology    : 5
% 1.94/1.22  #SimpNegUnit  : 2
% 1.94/1.22  #BackRed      : 0
% 1.94/1.22  
% 1.94/1.22  #Partial instantiations: 0
% 1.94/1.22  #Strategies tried      : 1
% 1.94/1.22  
% 1.94/1.22  Timing (in seconds)
% 1.94/1.22  ----------------------
% 1.94/1.23  Preprocessing        : 0.27
% 1.94/1.23  Parsing              : 0.15
% 1.94/1.23  CNF conversion       : 0.02
% 1.94/1.23  Main loop            : 0.13
% 1.94/1.23  Inferencing          : 0.05
% 1.94/1.23  Reduction            : 0.04
% 1.94/1.23  Demodulation         : 0.03
% 1.94/1.23  BG Simplification    : 0.01
% 1.94/1.23  Subsumption          : 0.03
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.42
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

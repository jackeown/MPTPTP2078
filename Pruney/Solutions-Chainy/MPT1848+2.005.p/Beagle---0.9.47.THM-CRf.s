%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:54 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   44 (  80 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 ( 143 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_33,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(c_24,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    ! [A_20] :
      ( u1_struct_0(A_20) = k2_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_4,c_30])).

tff(c_39,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_49,plain,(
    ! [A_21] :
      ( ~ v1_subset_1(k2_struct_0(A_21),u1_struct_0(A_21))
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_55,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_49])).

tff(c_61,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_64,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_61])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_64])).

tff(c_69,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_22,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    v1_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_40,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_20])).

tff(c_8,plain,(
    ! [B_6,A_4] :
      ( m1_subset_1(u1_struct_0(B_6),k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ m1_pre_topc(B_6,A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_142,plain,(
    ! [B_35,A_36] :
      ( v1_subset_1(u1_struct_0(B_35),u1_struct_0(A_36))
      | ~ m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ v1_tex_2(B_35,A_36)
      | ~ m1_pre_topc(B_35,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_164,plain,(
    ! [B_37,A_38] :
      ( v1_subset_1(u1_struct_0(B_37),u1_struct_0(A_38))
      | ~ v1_tex_2(B_37,A_38)
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_176,plain,(
    ! [B_37] :
      ( v1_subset_1(u1_struct_0(B_37),k2_struct_0('#skF_2'))
      | ~ v1_tex_2(B_37,'#skF_2')
      | ~ m1_pre_topc(B_37,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_164])).

tff(c_179,plain,(
    ! [B_39] :
      ( v1_subset_1(u1_struct_0(B_39),k2_struct_0('#skF_2'))
      | ~ v1_tex_2(B_39,'#skF_2')
      | ~ m1_pre_topc(B_39,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_176])).

tff(c_182,plain,
    ( v1_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2'))
    | ~ v1_tex_2('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_179])).

tff(c_187,plain,(
    v1_subset_1(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_18,c_182])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.45  
% 2.29/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.45  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.29/1.45  
% 2.29/1.45  %Foreground sorts:
% 2.29/1.45  
% 2.29/1.45  
% 2.29/1.45  %Background operators:
% 2.29/1.45  
% 2.29/1.45  
% 2.29/1.45  %Foreground operators:
% 2.29/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.45  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.29/1.45  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.29/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.45  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.29/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.29/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.29/1.45  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.29/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.45  
% 2.34/1.46  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.34/1.46  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.34/1.46  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.34/1.46  tff(f_38, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.34/1.46  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.34/1.46  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 2.34/1.46  tff(c_24, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.46  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.46  tff(c_30, plain, (![A_19]: (u1_struct_0(A_19)=k2_struct_0(A_19) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.46  tff(c_35, plain, (![A_20]: (u1_struct_0(A_20)=k2_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_4, c_30])).
% 2.34/1.46  tff(c_39, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_24, c_35])).
% 2.34/1.46  tff(c_49, plain, (![A_21]: (~v1_subset_1(k2_struct_0(A_21), u1_struct_0(A_21)) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.46  tff(c_55, plain, (~v1_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_39, c_49])).
% 2.34/1.46  tff(c_61, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_55])).
% 2.34/1.46  tff(c_64, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_61])).
% 2.34/1.46  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_64])).
% 2.34/1.46  tff(c_69, plain, (~v1_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_55])).
% 2.34/1.46  tff(c_22, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.46  tff(c_18, plain, (v1_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.46  tff(c_20, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.46  tff(c_40, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_39, c_20])).
% 2.34/1.46  tff(c_8, plain, (![B_6, A_4]: (m1_subset_1(u1_struct_0(B_6), k1_zfmisc_1(u1_struct_0(A_4))) | ~m1_pre_topc(B_6, A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.34/1.46  tff(c_142, plain, (![B_35, A_36]: (v1_subset_1(u1_struct_0(B_35), u1_struct_0(A_36)) | ~m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0(A_36))) | ~v1_tex_2(B_35, A_36) | ~m1_pre_topc(B_35, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.34/1.46  tff(c_164, plain, (![B_37, A_38]: (v1_subset_1(u1_struct_0(B_37), u1_struct_0(A_38)) | ~v1_tex_2(B_37, A_38) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(resolution, [status(thm)], [c_8, c_142])).
% 2.34/1.46  tff(c_176, plain, (![B_37]: (v1_subset_1(u1_struct_0(B_37), k2_struct_0('#skF_2')) | ~v1_tex_2(B_37, '#skF_2') | ~m1_pre_topc(B_37, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_39, c_164])).
% 2.34/1.46  tff(c_179, plain, (![B_39]: (v1_subset_1(u1_struct_0(B_39), k2_struct_0('#skF_2')) | ~v1_tex_2(B_39, '#skF_2') | ~m1_pre_topc(B_39, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_176])).
% 2.34/1.46  tff(c_182, plain, (v1_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2')) | ~v1_tex_2('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_40, c_179])).
% 2.34/1.46  tff(c_187, plain, (v1_subset_1(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_18, c_182])).
% 2.34/1.46  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_187])).
% 2.34/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.46  
% 2.34/1.46  Inference rules
% 2.34/1.46  ----------------------
% 2.34/1.46  #Ref     : 0
% 2.34/1.46  #Sup     : 38
% 2.34/1.46  #Fact    : 0
% 2.34/1.46  #Define  : 0
% 2.34/1.46  #Split   : 3
% 2.34/1.46  #Chain   : 0
% 2.34/1.46  #Close   : 0
% 2.34/1.46  
% 2.34/1.46  Ordering : KBO
% 2.34/1.46  
% 2.34/1.46  Simplification rules
% 2.34/1.46  ----------------------
% 2.34/1.46  #Subsume      : 9
% 2.34/1.46  #Demod        : 22
% 2.34/1.46  #Tautology    : 8
% 2.34/1.46  #SimpNegUnit  : 1
% 2.34/1.46  #BackRed      : 1
% 2.34/1.46  
% 2.34/1.46  #Partial instantiations: 0
% 2.34/1.46  #Strategies tried      : 1
% 2.34/1.46  
% 2.34/1.47  Timing (in seconds)
% 2.34/1.47  ----------------------
% 2.34/1.47  Preprocessing        : 0.45
% 2.34/1.47  Parsing              : 0.24
% 2.34/1.47  CNF conversion       : 0.03
% 2.34/1.47  Main loop            : 0.20
% 2.34/1.47  Inferencing          : 0.07
% 2.34/1.47  Reduction            : 0.06
% 2.34/1.47  Demodulation         : 0.04
% 2.34/1.47  BG Simplification    : 0.01
% 2.34/1.47  Subsumption          : 0.03
% 2.34/1.47  Abstraction          : 0.01
% 2.34/1.47  MUC search           : 0.00
% 2.34/1.47  Cooper               : 0.00
% 2.34/1.47  Total                : 0.68
% 2.34/1.47  Index Insertion      : 0.00
% 2.34/1.47  Index Deletion       : 0.00
% 2.34/1.47  Index Matching       : 0.00
% 2.34/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

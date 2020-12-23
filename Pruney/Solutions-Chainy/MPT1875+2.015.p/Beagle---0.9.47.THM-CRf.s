%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:48 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 124 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_63,axiom,(
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

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_25] :
      ( v2_tex_2(u1_struct_0(A_25),A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ m1_subset_1(u1_struct_0(A_25),k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_25] :
      ( v2_tex_2(u1_struct_0(A_25),A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ r1_tarski(u1_struct_0(A_25),u1_struct_0(A_25)) ) ),
    inference(resolution,[status(thm)],[c_10,c_60])).

tff(c_66,plain,(
    ! [A_25] :
      ( v2_tex_2(u1_struct_0(A_25),A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ l1_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_63])).

tff(c_18,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_40,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_32])).

tff(c_72,plain,(
    ! [C_27,A_28,B_29] :
      ( v2_tex_2(C_27,A_28)
      | ~ v2_tex_2(B_29,A_28)
      | ~ r1_tarski(C_27,B_29)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [A_30] :
      ( v2_tex_2('#skF_2',A_30)
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_30)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(u1_struct_0('#skF_1'),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_84,plain,(
    ! [A_31] :
      ( v2_tex_2('#skF_2',A_31)
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_31)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ r1_tarski(u1_struct_0('#skF_1'),u1_struct_0(A_31)) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_88,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_84])).

tff(c_91,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_88])).

tff(c_92,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_91])).

tff(c_95,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_92])).

tff(c_98,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_95])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.15  %$ v2_tex_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.79/1.15  
% 1.79/1.15  %Foreground sorts:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Background operators:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Foreground operators:
% 1.79/1.15  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.15  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.79/1.15  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.79/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.15  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.79/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.15  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.79/1.15  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.79/1.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.15  
% 2.06/1.16  tff(f_78, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.06/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.16  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.16  tff(f_49, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tex_2)).
% 2.06/1.16  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 2.06/1.16  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.16  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.16  tff(c_24, plain, (v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.16  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.16  tff(c_60, plain, (![A_25]: (v2_tex_2(u1_struct_0(A_25), A_25) | ~v1_tdlat_3(A_25) | ~m1_subset_1(u1_struct_0(A_25), k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.16  tff(c_63, plain, (![A_25]: (v2_tex_2(u1_struct_0(A_25), A_25) | ~v1_tdlat_3(A_25) | ~l1_pre_topc(A_25) | v2_struct_0(A_25) | ~r1_tarski(u1_struct_0(A_25), u1_struct_0(A_25)))), inference(resolution, [status(thm)], [c_10, c_60])).
% 2.06/1.16  tff(c_66, plain, (![A_25]: (v2_tex_2(u1_struct_0(A_25), A_25) | ~v1_tdlat_3(A_25) | ~l1_pre_topc(A_25) | v2_struct_0(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_63])).
% 2.06/1.16  tff(c_18, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.16  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.16  tff(c_32, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.16  tff(c_40, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_32])).
% 2.06/1.16  tff(c_72, plain, (![C_27, A_28, B_29]: (v2_tex_2(C_27, A_28) | ~v2_tex_2(B_29, A_28) | ~r1_tarski(C_27, B_29) | ~m1_subset_1(C_27, k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.16  tff(c_79, plain, (![A_30]: (v2_tex_2('#skF_2', A_30) | ~v2_tex_2(u1_struct_0('#skF_1'), A_30) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(u1_struct_0('#skF_1'), k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_40, c_72])).
% 2.06/1.16  tff(c_84, plain, (![A_31]: (v2_tex_2('#skF_2', A_31) | ~v2_tex_2(u1_struct_0('#skF_1'), A_31) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~r1_tarski(u1_struct_0('#skF_1'), u1_struct_0(A_31)))), inference(resolution, [status(thm)], [c_10, c_79])).
% 2.06/1.16  tff(c_88, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_6, c_84])).
% 2.06/1.16  tff(c_91, plain, (v2_tex_2('#skF_2', '#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_88])).
% 2.06/1.16  tff(c_92, plain, (~v2_tex_2(u1_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_18, c_91])).
% 2.06/1.16  tff(c_95, plain, (~v1_tdlat_3('#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_66, c_92])).
% 2.06/1.16  tff(c_98, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_95])).
% 2.06/1.16  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_98])).
% 2.06/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.16  
% 2.06/1.16  Inference rules
% 2.06/1.16  ----------------------
% 2.06/1.16  #Ref     : 0
% 2.06/1.16  #Sup     : 12
% 2.06/1.16  #Fact    : 0
% 2.06/1.16  #Define  : 0
% 2.06/1.16  #Split   : 1
% 2.06/1.16  #Chain   : 0
% 2.06/1.16  #Close   : 0
% 2.06/1.16  
% 2.06/1.16  Ordering : KBO
% 2.06/1.16  
% 2.06/1.16  Simplification rules
% 2.06/1.16  ----------------------
% 2.06/1.16  #Subsume      : 2
% 2.06/1.16  #Demod        : 8
% 2.06/1.16  #Tautology    : 5
% 2.06/1.16  #SimpNegUnit  : 2
% 2.06/1.16  #BackRed      : 0
% 2.06/1.16  
% 2.06/1.16  #Partial instantiations: 0
% 2.06/1.16  #Strategies tried      : 1
% 2.06/1.16  
% 2.06/1.16  Timing (in seconds)
% 2.06/1.16  ----------------------
% 2.06/1.16  Preprocessing        : 0.27
% 2.06/1.16  Parsing              : 0.15
% 2.06/1.16  CNF conversion       : 0.02
% 2.06/1.16  Main loop            : 0.14
% 2.06/1.16  Inferencing          : 0.06
% 2.06/1.16  Reduction            : 0.04
% 2.06/1.16  Demodulation         : 0.03
% 2.06/1.16  BG Simplification    : 0.01
% 2.06/1.17  Subsumption          : 0.03
% 2.06/1.17  Abstraction          : 0.01
% 2.06/1.17  MUC search           : 0.00
% 2.06/1.17  Cooper               : 0.00
% 2.06/1.17  Total                : 0.44
% 2.06/1.17  Index Insertion      : 0.00
% 2.06/1.17  Index Deletion       : 0.00
% 2.06/1.17  Index Matching       : 0.00
% 2.06/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

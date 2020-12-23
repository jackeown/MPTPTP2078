%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:54 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 144 expanded)
%              Number of leaves         :   21 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 277 expanded)
%              Number of equality atoms :   11 (  65 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ~ ( u1_struct_0(B) = u1_struct_0(A)
                & v1_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_tex_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

tff(f_45,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ~ v1_subset_1(k2_struct_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v1_subset_1(C,u1_struct_0(A))
                <=> v1_tex_2(B,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tex_2)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_47,plain,(
    ! [B_21,A_22] :
      ( l1_pre_topc(B_21)
      | ~ m1_pre_topc(B_21,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_47])).

tff(c_53,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_50])).

tff(c_4,plain,(
    ! [A_2] :
      ( l1_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_19] :
      ( u1_struct_0(A_19) = k2_struct_0(A_19)
      | ~ l1_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    ! [A_20] :
      ( u1_struct_0(A_20) = k2_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_4,c_28])).

tff(c_37,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_33])).

tff(c_18,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_18])).

tff(c_32,plain,(
    ! [A_2] :
      ( u1_struct_0(A_2) = k2_struct_0(A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_28])).

tff(c_56,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_53,c_32])).

tff(c_58,plain,(
    k2_struct_0('#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_56])).

tff(c_63,plain,(
    ! [A_23] :
      ( ~ v1_subset_1(k2_struct_0(A_23),u1_struct_0(A_23))
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_63])).

tff(c_73,plain,
    ( ~ v1_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_66])).

tff(c_75,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_78,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_75])).

tff(c_82,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_78])).

tff(c_83,plain,(
    ~ v1_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_16,plain,(
    v1_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( m1_subset_1(u1_struct_0(B_9),k1_zfmisc_1(u1_struct_0(A_7)))
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_228,plain,(
    ! [B_38,A_39] :
      ( v1_subset_1(u1_struct_0(B_38),u1_struct_0(A_39))
      | ~ v1_tex_2(B_38,A_39)
      | ~ m1_subset_1(u1_struct_0(B_38),k1_zfmisc_1(u1_struct_0(A_39)))
      | ~ m1_pre_topc(B_38,A_39)
      | ~ l1_pre_topc(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_251,plain,(
    ! [B_40,A_41] :
      ( v1_subset_1(u1_struct_0(B_40),u1_struct_0(A_41))
      | ~ v1_tex_2(B_40,A_41)
      | ~ m1_pre_topc(B_40,A_41)
      | ~ l1_pre_topc(A_41) ) ),
    inference(resolution,[status(thm)],[c_10,c_228])).

tff(c_290,plain,(
    ! [A_43] :
      ( v1_subset_1(k2_struct_0('#skF_1'),u1_struct_0(A_43))
      | ~ v1_tex_2('#skF_2',A_43)
      | ~ m1_pre_topc('#skF_2',A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_251])).

tff(c_306,plain,
    ( v1_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'))
    | ~ v1_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_290])).

tff(c_316,plain,(
    v1_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_16,c_306])).

tff(c_318,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  
% 2.14/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.29  %$ v1_tex_2 > v1_subset_1 > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.14/1.29  
% 2.14/1.29  %Foreground sorts:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Background operators:
% 2.14/1.29  
% 2.14/1.29  
% 2.14/1.29  %Foreground operators:
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.14/1.29  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.14/1.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.14/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.29  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.14/1.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.14/1.29  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.14/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.29  
% 2.14/1.30  tff(f_77, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => ~((u1_struct_0(B) = u1_struct_0(A)) & v1_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_tex_2)).
% 2.14/1.30  tff(f_40, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.14/1.30  tff(f_33, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.14/1.30  tff(f_29, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.14/1.30  tff(f_45, axiom, (![A]: (l1_struct_0(A) => ~v1_subset_1(k2_struct_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_struct_0)).
% 2.14/1.30  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.14/1.30  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v1_subset_1(C, u1_struct_0(A)) <=> v1_tex_2(B, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tex_2)).
% 2.14/1.30  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.30  tff(c_20, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.30  tff(c_47, plain, (![B_21, A_22]: (l1_pre_topc(B_21) | ~m1_pre_topc(B_21, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.14/1.30  tff(c_50, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_47])).
% 2.14/1.30  tff(c_53, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_50])).
% 2.14/1.30  tff(c_4, plain, (![A_2]: (l1_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.30  tff(c_28, plain, (![A_19]: (u1_struct_0(A_19)=k2_struct_0(A_19) | ~l1_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.30  tff(c_33, plain, (![A_20]: (u1_struct_0(A_20)=k2_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_4, c_28])).
% 2.14/1.30  tff(c_37, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_22, c_33])).
% 2.14/1.30  tff(c_18, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.30  tff(c_38, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_18])).
% 2.14/1.30  tff(c_32, plain, (![A_2]: (u1_struct_0(A_2)=k2_struct_0(A_2) | ~l1_pre_topc(A_2))), inference(resolution, [status(thm)], [c_4, c_28])).
% 2.14/1.30  tff(c_56, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_53, c_32])).
% 2.14/1.30  tff(c_58, plain, (k2_struct_0('#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_56])).
% 2.14/1.30  tff(c_63, plain, (![A_23]: (~v1_subset_1(k2_struct_0(A_23), u1_struct_0(A_23)) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.30  tff(c_66, plain, (~v1_subset_1(k2_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_63])).
% 2.14/1.30  tff(c_73, plain, (~v1_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_66])).
% 2.14/1.30  tff(c_75, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_73])).
% 2.14/1.30  tff(c_78, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_75])).
% 2.14/1.30  tff(c_82, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_78])).
% 2.14/1.30  tff(c_83, plain, (~v1_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_73])).
% 2.14/1.30  tff(c_16, plain, (v1_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.14/1.30  tff(c_10, plain, (![B_9, A_7]: (m1_subset_1(u1_struct_0(B_9), k1_zfmisc_1(u1_struct_0(A_7))) | ~m1_pre_topc(B_9, A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.14/1.30  tff(c_228, plain, (![B_38, A_39]: (v1_subset_1(u1_struct_0(B_38), u1_struct_0(A_39)) | ~v1_tex_2(B_38, A_39) | ~m1_subset_1(u1_struct_0(B_38), k1_zfmisc_1(u1_struct_0(A_39))) | ~m1_pre_topc(B_38, A_39) | ~l1_pre_topc(A_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.30  tff(c_251, plain, (![B_40, A_41]: (v1_subset_1(u1_struct_0(B_40), u1_struct_0(A_41)) | ~v1_tex_2(B_40, A_41) | ~m1_pre_topc(B_40, A_41) | ~l1_pre_topc(A_41))), inference(resolution, [status(thm)], [c_10, c_228])).
% 2.14/1.30  tff(c_290, plain, (![A_43]: (v1_subset_1(k2_struct_0('#skF_1'), u1_struct_0(A_43)) | ~v1_tex_2('#skF_2', A_43) | ~m1_pre_topc('#skF_2', A_43) | ~l1_pre_topc(A_43))), inference(superposition, [status(thm), theory('equality')], [c_38, c_251])).
% 2.14/1.30  tff(c_306, plain, (v1_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1')) | ~v1_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_37, c_290])).
% 2.14/1.30  tff(c_316, plain, (v1_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_16, c_306])).
% 2.14/1.30  tff(c_318, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_316])).
% 2.14/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  Inference rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Ref     : 0
% 2.14/1.30  #Sup     : 65
% 2.14/1.30  #Fact    : 0
% 2.14/1.30  #Define  : 0
% 2.14/1.30  #Split   : 2
% 2.14/1.30  #Chain   : 0
% 2.14/1.30  #Close   : 0
% 2.14/1.30  
% 2.14/1.30  Ordering : KBO
% 2.14/1.30  
% 2.14/1.30  Simplification rules
% 2.14/1.30  ----------------------
% 2.14/1.30  #Subsume      : 15
% 2.14/1.30  #Demod        : 55
% 2.14/1.30  #Tautology    : 19
% 2.14/1.30  #SimpNegUnit  : 4
% 2.14/1.30  #BackRed      : 1
% 2.14/1.30  
% 2.14/1.30  #Partial instantiations: 0
% 2.14/1.30  #Strategies tried      : 1
% 2.14/1.30  
% 2.14/1.30  Timing (in seconds)
% 2.14/1.30  ----------------------
% 2.14/1.31  Preprocessing        : 0.31
% 2.14/1.31  Parsing              : 0.16
% 2.14/1.31  CNF conversion       : 0.02
% 2.14/1.31  Main loop            : 0.22
% 2.14/1.31  Inferencing          : 0.08
% 2.14/1.31  Reduction            : 0.07
% 2.14/1.31  Demodulation         : 0.05
% 2.14/1.31  BG Simplification    : 0.01
% 2.14/1.31  Subsumption          : 0.04
% 2.14/1.31  Abstraction          : 0.01
% 2.14/1.31  MUC search           : 0.00
% 2.14/1.31  Cooper               : 0.00
% 2.14/1.31  Total                : 0.56
% 2.14/1.31  Index Insertion      : 0.00
% 2.14/1.31  Index Deletion       : 0.00
% 2.14/1.31  Index Matching       : 0.00
% 2.14/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

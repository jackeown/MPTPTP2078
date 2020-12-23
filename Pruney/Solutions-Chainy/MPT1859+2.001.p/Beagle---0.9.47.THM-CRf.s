%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:09 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   46 (  90 expanded)
%              Number of leaves         :   16 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 269 expanded)
%              Number of equality atoms :    3 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( B = u1_struct_0(A)
             => ( v2_tex_2(B,A)
              <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(c_12,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_pre_topc(A_1,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    u1_struct_0('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_23,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_16,plain,
    ( ~ v1_tdlat_3('#skF_1')
    | ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ~ v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_22,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | v1_tdlat_3('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_29,plain,(
    v1_tdlat_3('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_22])).

tff(c_50,plain,(
    ! [B_14,A_15] :
      ( v2_tex_2(u1_struct_0(B_14),A_15)
      | ~ v1_tdlat_3(B_14)
      | ~ m1_subset_1(u1_struct_0(B_14),k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_pre_topc(B_14,A_15)
      | v2_struct_0(B_14)
      | ~ l1_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_53,plain,(
    ! [A_15] :
      ( v2_tex_2(u1_struct_0('#skF_1'),A_15)
      | ~ v1_tdlat_3('#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_pre_topc('#skF_1',A_15)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_50])).

tff(c_58,plain,(
    ! [A_15] :
      ( v2_tex_2('#skF_2',A_15)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ m1_pre_topc('#skF_1',A_15)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_8,c_53])).

tff(c_63,plain,(
    ! [A_16] :
      ( v2_tex_2('#skF_2',A_16)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc('#skF_1',A_16)
      | ~ l1_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_58])).

tff(c_66,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_63])).

tff(c_68,plain,
    ( v2_tex_2('#skF_2','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_23,c_66])).

tff(c_69,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_28,c_68])).

tff(c_72,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_69])).

tff(c_76,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_72])).

tff(c_78,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_77,plain,(
    ~ v1_tdlat_3('#skF_1') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_82,plain,(
    ! [B_18,A_19] :
      ( v1_tdlat_3(B_18)
      | ~ v2_tex_2(u1_struct_0(B_18),A_19)
      | ~ m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_pre_topc(B_18,A_19)
      | v2_struct_0(B_18)
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    ! [A_19] :
      ( v1_tdlat_3('#skF_1')
      | ~ v2_tex_2(u1_struct_0('#skF_1'),A_19)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_pre_topc('#skF_1',A_19)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_82])).

tff(c_89,plain,(
    ! [A_19] :
      ( v1_tdlat_3('#skF_1')
      | ~ v2_tex_2('#skF_2',A_19)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_pre_topc('#skF_1',A_19)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_85])).

tff(c_94,plain,(
    ! [A_20] :
      ( ~ v2_tex_2('#skF_2',A_20)
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_pre_topc('#skF_1',A_20)
      | ~ l1_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_77,c_89])).

tff(c_97,plain,
    ( ~ v2_tex_2('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2'))
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_94])).

tff(c_99,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_23,c_78,c_97])).

tff(c_100,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_99])).

tff(c_103,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:46:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.24  
% 1.87/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.24  %$ v2_tex_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.87/1.24  
% 1.87/1.24  %Foreground sorts:
% 1.87/1.24  
% 1.87/1.24  
% 1.87/1.24  %Background operators:
% 1.87/1.24  
% 1.87/1.24  
% 1.87/1.24  %Foreground operators:
% 1.87/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.87/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.24  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.87/1.24  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 1.87/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.24  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 1.87/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.24  
% 1.96/1.25  tff(f_64, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 1.96/1.25  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 1.96/1.25  tff(f_49, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 1.96/1.25  tff(c_12, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.25  tff(c_2, plain, (![A_1]: (m1_pre_topc(A_1, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.25  tff(c_14, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.25  tff(c_8, plain, (u1_struct_0('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.25  tff(c_10, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.25  tff(c_23, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.96/1.25  tff(c_16, plain, (~v1_tdlat_3('#skF_1') | ~v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.25  tff(c_28, plain, (~v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_16])).
% 1.96/1.25  tff(c_22, plain, (v2_tex_2('#skF_2', '#skF_1') | v1_tdlat_3('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.96/1.25  tff(c_29, plain, (v1_tdlat_3('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_28, c_22])).
% 1.96/1.25  tff(c_50, plain, (![B_14, A_15]: (v2_tex_2(u1_struct_0(B_14), A_15) | ~v1_tdlat_3(B_14) | ~m1_subset_1(u1_struct_0(B_14), k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_pre_topc(B_14, A_15) | v2_struct_0(B_14) | ~l1_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.25  tff(c_53, plain, (![A_15]: (v2_tex_2(u1_struct_0('#skF_1'), A_15) | ~v1_tdlat_3('#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_pre_topc('#skF_1', A_15) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_15) | v2_struct_0(A_15))), inference(superposition, [status(thm), theory('equality')], [c_8, c_50])).
% 1.96/1.25  tff(c_58, plain, (![A_15]: (v2_tex_2('#skF_2', A_15) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_15))) | ~m1_pre_topc('#skF_1', A_15) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_15) | v2_struct_0(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_8, c_53])).
% 1.96/1.25  tff(c_63, plain, (![A_16]: (v2_tex_2('#skF_2', A_16) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc('#skF_1', A_16) | ~l1_pre_topc(A_16) | v2_struct_0(A_16))), inference(negUnitSimplification, [status(thm)], [c_14, c_58])).
% 1.96/1.25  tff(c_66, plain, (v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_63])).
% 1.96/1.25  tff(c_68, plain, (v2_tex_2('#skF_2', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_23, c_66])).
% 1.96/1.25  tff(c_69, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_14, c_28, c_68])).
% 1.96/1.25  tff(c_72, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_69])).
% 1.96/1.25  tff(c_76, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_72])).
% 1.96/1.25  tff(c_78, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_16])).
% 1.96/1.25  tff(c_77, plain, (~v1_tdlat_3('#skF_1')), inference(splitRight, [status(thm)], [c_16])).
% 1.96/1.25  tff(c_82, plain, (![B_18, A_19]: (v1_tdlat_3(B_18) | ~v2_tex_2(u1_struct_0(B_18), A_19) | ~m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_pre_topc(B_18, A_19) | v2_struct_0(B_18) | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.25  tff(c_85, plain, (![A_19]: (v1_tdlat_3('#skF_1') | ~v2_tex_2(u1_struct_0('#skF_1'), A_19) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_pre_topc('#skF_1', A_19) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(superposition, [status(thm), theory('equality')], [c_8, c_82])).
% 1.96/1.25  tff(c_89, plain, (![A_19]: (v1_tdlat_3('#skF_1') | ~v2_tex_2('#skF_2', A_19) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_pre_topc('#skF_1', A_19) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_19) | v2_struct_0(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_85])).
% 1.96/1.25  tff(c_94, plain, (![A_20]: (~v2_tex_2('#skF_2', A_20) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_pre_topc('#skF_1', A_20) | ~l1_pre_topc(A_20) | v2_struct_0(A_20))), inference(negUnitSimplification, [status(thm)], [c_14, c_77, c_89])).
% 1.96/1.25  tff(c_97, plain, (~v2_tex_2('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2')) | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8, c_94])).
% 1.96/1.25  tff(c_99, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_23, c_78, c_97])).
% 1.96/1.25  tff(c_100, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_14, c_99])).
% 1.96/1.25  tff(c_103, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_100])).
% 1.96/1.25  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_103])).
% 1.96/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  Inference rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Ref     : 0
% 1.96/1.25  #Sup     : 13
% 1.96/1.25  #Fact    : 0
% 1.96/1.25  #Define  : 0
% 1.96/1.25  #Split   : 1
% 1.96/1.25  #Chain   : 0
% 1.96/1.25  #Close   : 0
% 1.96/1.25  
% 1.96/1.25  Ordering : KBO
% 1.96/1.25  
% 1.96/1.25  Simplification rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Subsume      : 1
% 1.96/1.25  #Demod        : 20
% 1.96/1.25  #Tautology    : 6
% 1.96/1.25  #SimpNegUnit  : 11
% 1.96/1.25  #BackRed      : 0
% 1.96/1.25  
% 1.96/1.25  #Partial instantiations: 0
% 1.96/1.25  #Strategies tried      : 1
% 1.96/1.25  
% 1.96/1.25  Timing (in seconds)
% 1.96/1.25  ----------------------
% 1.96/1.25  Preprocessing        : 0.31
% 1.96/1.25  Parsing              : 0.18
% 1.96/1.25  CNF conversion       : 0.02
% 1.96/1.25  Main loop            : 0.17
% 1.96/1.25  Inferencing          : 0.06
% 1.96/1.25  Reduction            : 0.05
% 1.96/1.25  Demodulation         : 0.03
% 1.96/1.25  BG Simplification    : 0.01
% 1.96/1.25  Subsumption          : 0.03
% 1.96/1.25  Abstraction          : 0.01
% 1.96/1.25  MUC search           : 0.00
% 1.96/1.25  Cooper               : 0.00
% 1.96/1.25  Total                : 0.51
% 1.96/1.25  Index Insertion      : 0.00
% 1.96/1.25  Index Deletion       : 0.00
% 1.96/1.25  Index Matching       : 0.00
% 1.96/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

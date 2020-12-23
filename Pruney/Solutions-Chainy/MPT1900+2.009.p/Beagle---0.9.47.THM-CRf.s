%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:36 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 167 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => v5_pre_topc(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r1_tarski(k8_relset_1(A,B,D,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(c_28,plain,(
    ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_129,plain,(
    ! [A_59,B_60,D_61,C_62] :
      ( r1_tarski(k8_relset_1(A_59,B_60,D_61,C_62),A_59)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [C_62] :
      ( r1_tarski(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',C_62),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_129])).

tff(c_139,plain,(
    ! [C_63] : r1_tarski(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',C_63),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_134])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [B_51,A_52] :
      ( v4_pre_topc(B_51,A_52)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_52)))
      | ~ v1_tdlat_3(A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_109,plain,(
    ! [A_1,A_52] :
      ( v4_pre_topc(A_1,A_52)
      | ~ v1_tdlat_3(A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52)
      | ~ r1_tarski(A_1,u1_struct_0(A_52)) ) ),
    inference(resolution,[status(thm)],[c_4,c_97])).

tff(c_142,plain,(
    ! [C_63] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',C_63),'#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_139,c_109])).

tff(c_148,plain,(
    ! [C_63] : v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',C_63),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_42,c_142])).

tff(c_210,plain,(
    ! [A_72,B_73,C_74] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_72),u1_struct_0(B_73),C_74,'#skF_1'(A_72,B_73,C_74)),A_72)
      | v5_pre_topc(C_74,A_72,B_73)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72),u1_struct_0(B_73))))
      | ~ v1_funct_2(C_74,u1_struct_0(A_72),u1_struct_0(B_73))
      | ~ v1_funct_1(C_74)
      | ~ l1_pre_topc(B_73)
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_148,c_210])).

tff(c_217,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_34,c_32,c_30,c_214])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.38  
% 2.43/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.38  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > u1_pre_topc > k9_setfam_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4
% 2.43/1.38  
% 2.43/1.38  %Foreground sorts:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Background operators:
% 2.43/1.38  
% 2.43/1.38  
% 2.43/1.38  %Foreground operators:
% 2.43/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.43/1.38  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.43/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.43/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.38  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.43/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.43/1.38  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.43/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.38  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.43/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.43/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.38  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.38  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.43/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.43/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.43/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.38  
% 2.43/1.39  tff(f_96, negated_conjecture, ~(![A]: (((v2_pre_topc(A) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => v5_pre_topc(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tex_2)).
% 2.43/1.39  tff(f_37, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 2.43/1.39  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.43/1.39  tff(f_75, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tdlat_3)).
% 2.43/1.39  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.43/1.39  tff(c_28, plain, (~v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_36, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_42, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.43/1.39  tff(c_129, plain, (![A_59, B_60, D_61, C_62]: (r1_tarski(k8_relset_1(A_59, B_60, D_61, C_62), A_59) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.39  tff(c_134, plain, (![C_62]: (r1_tarski(k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', C_62), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_129])).
% 2.43/1.39  tff(c_139, plain, (![C_63]: (r1_tarski(k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', C_63), u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_134])).
% 2.43/1.39  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.39  tff(c_97, plain, (![B_51, A_52]: (v4_pre_topc(B_51, A_52) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_52))) | ~v1_tdlat_3(A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.43/1.39  tff(c_109, plain, (![A_1, A_52]: (v4_pre_topc(A_1, A_52) | ~v1_tdlat_3(A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52) | ~r1_tarski(A_1, u1_struct_0(A_52)))), inference(resolution, [status(thm)], [c_4, c_97])).
% 2.43/1.39  tff(c_142, plain, (![C_63]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', C_63), '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_139, c_109])).
% 2.43/1.39  tff(c_148, plain, (![C_63]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', C_63), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_42, c_142])).
% 2.43/1.39  tff(c_210, plain, (![A_72, B_73, C_74]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_72), u1_struct_0(B_73), C_74, '#skF_1'(A_72, B_73, C_74)), A_72) | v5_pre_topc(C_74, A_72, B_73) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72), u1_struct_0(B_73)))) | ~v1_funct_2(C_74, u1_struct_0(A_72), u1_struct_0(B_73)) | ~v1_funct_1(C_74) | ~l1_pre_topc(B_73) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.43/1.39  tff(c_214, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_148, c_210])).
% 2.43/1.39  tff(c_217, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_34, c_32, c_30, c_214])).
% 2.43/1.39  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_217])).
% 2.43/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.39  
% 2.43/1.39  Inference rules
% 2.43/1.39  ----------------------
% 2.43/1.39  #Ref     : 0
% 2.43/1.39  #Sup     : 33
% 2.43/1.39  #Fact    : 0
% 2.43/1.39  #Define  : 0
% 2.43/1.39  #Split   : 1
% 2.43/1.39  #Chain   : 0
% 2.43/1.39  #Close   : 0
% 2.43/1.39  
% 2.43/1.39  Ordering : KBO
% 2.43/1.39  
% 2.43/1.39  Simplification rules
% 2.43/1.39  ----------------------
% 2.43/1.39  #Subsume      : 1
% 2.43/1.39  #Demod        : 33
% 2.43/1.39  #Tautology    : 14
% 2.43/1.39  #SimpNegUnit  : 3
% 2.43/1.39  #BackRed      : 0
% 2.43/1.39  
% 2.43/1.39  #Partial instantiations: 0
% 2.43/1.39  #Strategies tried      : 1
% 2.43/1.39  
% 2.43/1.39  Timing (in seconds)
% 2.43/1.39  ----------------------
% 2.43/1.39  Preprocessing        : 0.36
% 2.43/1.39  Parsing              : 0.19
% 2.43/1.39  CNF conversion       : 0.03
% 2.43/1.39  Main loop            : 0.19
% 2.43/1.39  Inferencing          : 0.08
% 2.43/1.39  Reduction            : 0.06
% 2.43/1.39  Demodulation         : 0.04
% 2.43/1.39  BG Simplification    : 0.01
% 2.43/1.39  Subsumption          : 0.03
% 2.43/1.39  Abstraction          : 0.01
% 2.43/1.39  MUC search           : 0.00
% 2.43/1.39  Cooper               : 0.00
% 2.43/1.39  Total                : 0.57
% 2.43/1.39  Index Insertion      : 0.00
% 2.43/1.39  Index Deletion       : 0.00
% 2.43/1.39  Index Matching       : 0.00
% 2.43/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

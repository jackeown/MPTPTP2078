%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:36 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 148 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

tff(f_50,axiom,(
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

tff(c_18,plain,(
    ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_22,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k8_relset_1(A_1,B_2,C_3,D_4),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [B_41,A_42] :
      ( v4_pre_topc(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ v1_tdlat_3(A_42)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_48,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_43),B_44,C_45,D_46),A_43)
      | ~ v1_tdlat_3(A_43)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43),B_44))) ) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_53,plain,(
    ! [D_46] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_46),'#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_48])).

tff(c_57,plain,(
    ! [D_46] : v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',D_46),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_32,c_53])).

tff(c_88,plain,(
    ! [A_60,B_61,C_62] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_60),u1_struct_0(B_61),C_62,'#skF_1'(A_60,B_61,C_62)),A_60)
      | v5_pre_topc(C_62,A_60,B_61)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60),u1_struct_0(B_61))))
      | ~ v1_funct_2(C_62,u1_struct_0(A_60),u1_struct_0(B_61))
      | ~ v1_funct_1(C_62)
      | ~ l1_pre_topc(B_61)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_88])).

tff(c_100,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_24,c_22,c_20,c_96])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:10:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4
% 1.73/1.16  
% 1.73/1.16  %Foreground sorts:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Background operators:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Foreground operators:
% 1.73/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.73/1.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.73/1.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.16  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 1.73/1.16  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.73/1.16  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 1.73/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.73/1.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.73/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.73/1.16  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.16  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 1.73/1.16  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.73/1.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.73/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.73/1.16  
% 1.73/1.17  tff(f_82, negated_conjecture, ~(![A]: (((v2_pre_topc(A) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => v5_pre_topc(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_tex_2)).
% 1.73/1.17  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 1.73/1.17  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_tdlat_3)).
% 1.73/1.17  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 1.73/1.17  tff(c_18, plain, (~v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_30, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_26, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_24, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_22, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_34, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_32, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.73/1.17  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k8_relset_1(A_1, B_2, C_3, D_4), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.17  tff(c_38, plain, (![B_41, A_42]: (v4_pre_topc(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~v1_tdlat_3(A_42) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.73/1.17  tff(c_48, plain, (![A_43, B_44, C_45, D_46]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_43), B_44, C_45, D_46), A_43) | ~v1_tdlat_3(A_43) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_43), B_44))))), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.73/1.17  tff(c_53, plain, (![D_46]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_46), '#skF_3') | ~v1_tdlat_3('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_48])).
% 1.73/1.17  tff(c_57, plain, (![D_46]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_5', D_46), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_32, c_53])).
% 1.73/1.17  tff(c_88, plain, (![A_60, B_61, C_62]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_60), u1_struct_0(B_61), C_62, '#skF_1'(A_60, B_61, C_62)), A_60) | v5_pre_topc(C_62, A_60, B_61) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_60), u1_struct_0(B_61)))) | ~v1_funct_2(C_62, u1_struct_0(A_60), u1_struct_0(B_61)) | ~v1_funct_1(C_62) | ~l1_pre_topc(B_61) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.73/1.17  tff(c_96, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_57, c_88])).
% 1.73/1.17  tff(c_100, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_24, c_22, c_20, c_96])).
% 1.73/1.17  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_100])).
% 1.73/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  Inference rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Ref     : 0
% 1.73/1.17  #Sup     : 11
% 1.73/1.17  #Fact    : 0
% 1.73/1.17  #Define  : 0
% 1.73/1.17  #Split   : 0
% 1.73/1.17  #Chain   : 0
% 1.73/1.17  #Close   : 0
% 1.73/1.17  
% 1.73/1.17  Ordering : KBO
% 1.73/1.17  
% 1.73/1.17  Simplification rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Subsume      : 0
% 1.73/1.17  #Demod        : 19
% 1.73/1.17  #Tautology    : 2
% 1.73/1.17  #SimpNegUnit  : 3
% 1.73/1.17  #BackRed      : 0
% 1.73/1.17  
% 1.73/1.17  #Partial instantiations: 0
% 1.73/1.17  #Strategies tried      : 1
% 1.73/1.17  
% 1.73/1.17  Timing (in seconds)
% 1.73/1.17  ----------------------
% 1.73/1.18  Preprocessing        : 0.28
% 1.73/1.18  Parsing              : 0.16
% 1.73/1.18  CNF conversion       : 0.02
% 1.73/1.18  Main loop            : 0.16
% 1.73/1.18  Inferencing          : 0.07
% 1.73/1.18  Reduction            : 0.05
% 1.73/1.18  Demodulation         : 0.03
% 1.73/1.18  BG Simplification    : 0.01
% 1.73/1.18  Subsumption          : 0.02
% 1.73/1.18  Abstraction          : 0.01
% 1.73/1.18  MUC search           : 0.00
% 1.73/1.18  Cooper               : 0.00
% 1.73/1.18  Total                : 0.46
% 1.73/1.18  Index Insertion      : 0.00
% 1.73/1.18  Index Deletion       : 0.00
% 1.73/1.18  Index Matching       : 0.00
% 1.73/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

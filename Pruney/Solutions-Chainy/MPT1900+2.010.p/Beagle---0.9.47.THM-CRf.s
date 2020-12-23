%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:36 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 115 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 405 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v3_tdlat_3 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v3_tdlat_3,type,(
    v3_tdlat_3: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_108,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => v3_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v3_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tdlat_3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

tff(c_34,plain,(
    ~ v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_46,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_42,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_50,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,(
    v1_tdlat_3('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_32,plain,(
    ! [A_35] :
      ( m1_subset_1('#skF_4'(A_35),k1_zfmisc_1(u1_struct_0(A_35)))
      | v3_tdlat_3(A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60,plain,(
    ! [B_55,A_56] :
      ( v3_pre_topc(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ v1_tdlat_3(A_56)
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_96,plain,(
    ! [A_59] :
      ( v3_pre_topc('#skF_4'(A_59),A_59)
      | ~ v1_tdlat_3(A_59)
      | v3_tdlat_3(A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_32,c_60])).

tff(c_28,plain,(
    ! [A_35] :
      ( ~ v3_pre_topc('#skF_4'(A_35),A_35)
      | v3_tdlat_3(A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_100,plain,(
    ! [A_59] :
      ( ~ v1_tdlat_3(A_59)
      | v3_tdlat_3(A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(resolution,[status(thm)],[c_96,c_28])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k8_relset_1(A_1,B_2,C_3,D_4),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(A_64),B_65,C_66,D_67),A_64)
      | ~ v1_tdlat_3(A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64),B_65))) ) ),
    inference(resolution,[status(thm)],[c_2,c_60])).

tff(c_126,plain,(
    ! [D_67] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_67),'#skF_5')
      | ~ v1_tdlat_3('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_121])).

tff(c_130,plain,(
    ! [D_67] : v3_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_67),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_126])).

tff(c_78,plain,(
    ! [B_57,A_58] :
      ( v4_pre_topc(B_57,A_58)
      | ~ v3_pre_topc(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ v3_tdlat_3(A_58)
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_143,plain,(
    ! [A_72,B_73,C_74,D_75] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_72),B_73,C_74,D_75),A_72)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(A_72),B_73,C_74,D_75),A_72)
      | ~ v3_tdlat_3(A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72),B_73))) ) ),
    inference(resolution,[status(thm)],[c_2,c_78])).

tff(c_148,plain,(
    ! [D_75] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_75),'#skF_5')
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_75),'#skF_5')
      | ~ v3_tdlat_3('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_152,plain,(
    ! [D_75] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_75),'#skF_5')
      | ~ v3_tdlat_3('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_130,c_148])).

tff(c_153,plain,(
    ~ v3_tdlat_3('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_156,plain,
    ( ~ v1_tdlat_3('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_153])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_48,c_156])).

tff(c_161,plain,(
    ! [D_75] : v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'),'#skF_7',D_75),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_208,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_90),u1_struct_0(B_91),C_92,'#skF_1'(A_90,B_91,C_92)),A_90)
      | v5_pre_topc(C_92,A_90,B_91)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_90),u1_struct_0(B_91))))
      | ~ v1_funct_2(C_92,u1_struct_0(A_90),u1_struct_0(B_91))
      | ~ v1_funct_1(C_92)
      | ~ l1_pre_topc(B_91)
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_212,plain,
    ( v5_pre_topc('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_5'),u1_struct_0('#skF_6'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_161,c_208])).

tff(c_215,plain,(
    v5_pre_topc('#skF_7','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_40,c_38,c_36,c_212])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  
% 2.28/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.26  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v3_pre_topc > m1_subset_1 > v3_tdlat_3 > v2_pre_topc > v1_tdlat_3 > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3
% 2.28/1.26  
% 2.28/1.26  %Foreground sorts:
% 2.28/1.26  
% 2.28/1.26  
% 2.28/1.26  %Background operators:
% 2.28/1.26  
% 2.28/1.26  
% 2.28/1.26  %Foreground operators:
% 2.28/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.28/1.26  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.28/1.26  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.28/1.26  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.26  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.28/1.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.28/1.26  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.28/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.28/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.28/1.26  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.26  tff(v3_tdlat_3, type, v3_tdlat_3: $i > $o).
% 2.28/1.26  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.26  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.28/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.26  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.28/1.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.28/1.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.28/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.26  
% 2.28/1.28  tff(f_108, negated_conjecture, ~(![A]: (((v2_pre_topc(A) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => v5_pre_topc(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_tex_2)).
% 2.28/1.28  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => v3_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tdlat_3)).
% 2.28/1.28  tff(f_61, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_tdlat_3)).
% 2.28/1.28  tff(f_29, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 2.28/1.28  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v3_tdlat_3(A) <=> (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tdlat_3)).
% 2.28/1.28  tff(f_50, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_pre_topc)).
% 2.28/1.28  tff(c_34, plain, (~v5_pre_topc('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_46, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_42, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_38, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_36, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_50, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_48, plain, (v1_tdlat_3('#skF_5')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.28/1.28  tff(c_32, plain, (![A_35]: (m1_subset_1('#skF_4'(A_35), k1_zfmisc_1(u1_struct_0(A_35))) | v3_tdlat_3(A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.28/1.28  tff(c_60, plain, (![B_55, A_56]: (v3_pre_topc(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_56))) | ~v1_tdlat_3(A_56) | ~l1_pre_topc(A_56) | ~v2_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.28/1.28  tff(c_96, plain, (![A_59]: (v3_pre_topc('#skF_4'(A_59), A_59) | ~v1_tdlat_3(A_59) | v3_tdlat_3(A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(resolution, [status(thm)], [c_32, c_60])).
% 2.28/1.28  tff(c_28, plain, (![A_35]: (~v3_pre_topc('#skF_4'(A_35), A_35) | v3_tdlat_3(A_35) | ~l1_pre_topc(A_35) | ~v2_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.28/1.28  tff(c_100, plain, (![A_59]: (~v1_tdlat_3(A_59) | v3_tdlat_3(A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(resolution, [status(thm)], [c_96, c_28])).
% 2.28/1.28  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (m1_subset_1(k8_relset_1(A_1, B_2, C_3, D_4), k1_zfmisc_1(A_1)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.28  tff(c_121, plain, (![A_64, B_65, C_66, D_67]: (v3_pre_topc(k8_relset_1(u1_struct_0(A_64), B_65, C_66, D_67), A_64) | ~v1_tdlat_3(A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_64), B_65))))), inference(resolution, [status(thm)], [c_2, c_60])).
% 2.28/1.28  tff(c_126, plain, (![D_67]: (v3_pre_topc(k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'), '#skF_7', D_67), '#skF_5') | ~v1_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_121])).
% 2.28/1.28  tff(c_130, plain, (![D_67]: (v3_pre_topc(k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'), '#skF_7', D_67), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_126])).
% 2.28/1.28  tff(c_78, plain, (![B_57, A_58]: (v4_pre_topc(B_57, A_58) | ~v3_pre_topc(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~v3_tdlat_3(A_58) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.28/1.28  tff(c_143, plain, (![A_72, B_73, C_74, D_75]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_72), B_73, C_74, D_75), A_72) | ~v3_pre_topc(k8_relset_1(u1_struct_0(A_72), B_73, C_74, D_75), A_72) | ~v3_tdlat_3(A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_72), B_73))))), inference(resolution, [status(thm)], [c_2, c_78])).
% 2.28/1.28  tff(c_148, plain, (![D_75]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'), '#skF_7', D_75), '#skF_5') | ~v3_pre_topc(k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'), '#skF_7', D_75), '#skF_5') | ~v3_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_143])).
% 2.28/1.28  tff(c_152, plain, (![D_75]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'), '#skF_7', D_75), '#skF_5') | ~v3_tdlat_3('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_130, c_148])).
% 2.28/1.28  tff(c_153, plain, (~v3_tdlat_3('#skF_5')), inference(splitLeft, [status(thm)], [c_152])).
% 2.28/1.28  tff(c_156, plain, (~v1_tdlat_3('#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_100, c_153])).
% 2.28/1.28  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_48, c_156])).
% 2.28/1.28  tff(c_161, plain, (![D_75]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6'), '#skF_7', D_75), '#skF_5'))), inference(splitRight, [status(thm)], [c_152])).
% 2.28/1.28  tff(c_208, plain, (![A_90, B_91, C_92]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_90), u1_struct_0(B_91), C_92, '#skF_1'(A_90, B_91, C_92)), A_90) | v5_pre_topc(C_92, A_90, B_91) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_90), u1_struct_0(B_91)))) | ~v1_funct_2(C_92, u1_struct_0(A_90), u1_struct_0(B_91)) | ~v1_funct_1(C_92) | ~l1_pre_topc(B_91) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.28  tff(c_212, plain, (v5_pre_topc('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_6')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_5'), u1_struct_0('#skF_6')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_161, c_208])).
% 2.28/1.28  tff(c_215, plain, (v5_pre_topc('#skF_7', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_40, c_38, c_36, c_212])).
% 2.28/1.28  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_215])).
% 2.28/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.28  
% 2.28/1.28  Inference rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Ref     : 0
% 2.28/1.28  #Sup     : 28
% 2.28/1.28  #Fact    : 0
% 2.28/1.28  #Define  : 0
% 2.28/1.28  #Split   : 3
% 2.28/1.28  #Chain   : 0
% 2.28/1.28  #Close   : 0
% 2.28/1.28  
% 2.28/1.28  Ordering : KBO
% 2.28/1.28  
% 2.28/1.28  Simplification rules
% 2.28/1.28  ----------------------
% 2.28/1.28  #Subsume      : 6
% 2.28/1.28  #Demod        : 37
% 2.28/1.28  #Tautology    : 5
% 2.28/1.28  #SimpNegUnit  : 3
% 2.28/1.28  #BackRed      : 0
% 2.28/1.28  
% 2.28/1.28  #Partial instantiations: 0
% 2.28/1.28  #Strategies tried      : 1
% 2.28/1.28  
% 2.28/1.28  Timing (in seconds)
% 2.28/1.28  ----------------------
% 2.28/1.28  Preprocessing        : 0.30
% 2.28/1.28  Parsing              : 0.17
% 2.28/1.28  CNF conversion       : 0.02
% 2.28/1.28  Main loop            : 0.22
% 2.28/1.28  Inferencing          : 0.09
% 2.28/1.28  Reduction            : 0.06
% 2.28/1.28  Demodulation         : 0.04
% 2.28/1.28  BG Simplification    : 0.01
% 2.28/1.28  Subsumption          : 0.04
% 2.28/1.28  Abstraction          : 0.01
% 2.28/1.28  MUC search           : 0.00
% 2.28/1.28  Cooper               : 0.00
% 2.28/1.28  Total                : 0.55
% 2.28/1.28  Index Insertion      : 0.00
% 2.28/1.28  Index Deletion       : 0.00
% 2.28/1.28  Index Matching       : 0.00
% 2.28/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1902+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:40 EST 2020

% Result     : Theorem 5.88s
% Output     : CNFRefutation 6.14s
% Verified   : 
% Statistics : Number of formulae       :  142 (5835 expanded)
%              Number of leaves         :   41 (2049 expanded)
%              Depth                    :   25
%              Number of atoms          :  370 (20046 expanded)
%              Number of equality atoms :   54 (2443 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & v2_tdlat_3(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => v5_pre_topc(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tex_2)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_76,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_63,axiom,(
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

tff(f_110,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v2_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( v4_pre_topc(B,A)
                & B != k1_xboole_0
                & B != u1_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tdlat_3)).

tff(f_128,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( ( k2_struct_0(B) = k1_xboole_0
                 => k2_struct_0(A) = k1_xboole_0 )
               => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_22,plain,(
    ! [A_35] :
      ( v4_pre_topc(k2_struct_0(A_35),A_35)
      | ~ l1_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_18,plain,(
    ! [A_34] :
      ( l1_struct_0(A_34)
      | ~ l1_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_67,plain,(
    ! [A_61] :
      ( u1_struct_0(A_61) = k2_struct_0(A_61)
      | ~ l1_struct_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_77,plain,(
    ! [A_63] :
      ( u1_struct_0(A_63) = k2_struct_0(A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_85,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_77])).

tff(c_84,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_77])).

tff(c_48,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_87,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48])).

tff(c_96,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_87])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46])).

tff(c_106,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_86])).

tff(c_20,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    ! [A_36,B_37] : v1_relat_1(k2_zfmisc_1(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [B_6,A_4] :
      ( v1_relat_1(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_4))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_106,c_4])).

tff(c_112,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_109])).

tff(c_28,plain,(
    ! [A_42] :
      ( k10_relat_1(A_42,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_116,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_28])).

tff(c_151,plain,(
    ! [A_74,B_75,C_76,D_77] :
      ( k8_relset_1(A_74,B_75,C_76,D_77) = k10_relat_1(C_76,D_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_154,plain,(
    ! [D_77] : k8_relset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'),'#skF_5',D_77) = k10_relat_1('#skF_5',D_77) ),
    inference(resolution,[status(thm)],[c_106,c_151])).

tff(c_181,plain,(
    ! [A_83,B_84,C_85,D_86] :
      ( m1_subset_1(k8_relset_1(A_83,B_84,C_85,D_86),k1_zfmisc_1(A_83))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_202,plain,(
    ! [D_77] :
      ( m1_subset_1(k10_relat_1('#skF_5',D_77),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_181])).

tff(c_219,plain,(
    ! [D_90] : m1_subset_1(k10_relat_1('#skF_5',D_90),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_202])).

tff(c_227,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_219])).

tff(c_164,plain,(
    ! [B_79,A_80] :
      ( v4_pre_topc(B_79,A_80)
      | ~ v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_173,plain,(
    ! [B_79] :
      ( v4_pre_topc(B_79,'#skF_3')
      | ~ v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_164])).

tff(c_178,plain,(
    ! [B_79] :
      ( v4_pre_topc(B_79,'#skF_3')
      | ~ v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_173])).

tff(c_232,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_3')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_227,c_178])).

tff(c_238,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_232])).

tff(c_320,plain,(
    ! [A_108,B_109,C_110] :
      ( v4_pre_topc('#skF_1'(A_108,B_109,C_110),B_109)
      | v5_pre_topc(C_110,A_108,B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),u1_struct_0(B_109))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0(B_109))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc(B_109)
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_327,plain,(
    ! [A_108,C_110] :
      ( v4_pre_topc('#skF_1'(A_108,'#skF_4',C_110),'#skF_4')
      | v5_pre_topc(C_110,A_108,'#skF_4')
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_108),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_110,u1_struct_0(A_108),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_110)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_320])).

tff(c_364,plain,(
    ! [A_124,C_125] :
      ( v4_pre_topc('#skF_1'(A_124,'#skF_4',C_125),'#skF_4')
      | v5_pre_topc(C_125,A_124,'#skF_4')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_124),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_125,u1_struct_0(A_124),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_125)
      | ~ l1_pre_topc(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85,c_327])).

tff(c_374,plain,(
    ! [C_125] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4',C_125),'#skF_4')
      | v5_pre_topc(C_125,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_125,u1_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_125)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_364])).

tff(c_386,plain,(
    ! [C_127] :
      ( v4_pre_topc('#skF_1'('#skF_3','#skF_4',C_127),'#skF_4')
      | v5_pre_topc(C_127,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_127,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_84,c_374])).

tff(c_393,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_106,c_386])).

tff(c_397,plain,
    ( v4_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4')
    | v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_96,c_393])).

tff(c_398,plain,(
    v4_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_397])).

tff(c_421,plain,(
    ! [A_131,B_132,C_133] :
      ( m1_subset_1('#skF_1'(A_131,B_132,C_133),k1_zfmisc_1(u1_struct_0(B_132)))
      | v5_pre_topc(C_133,A_131,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(B_132))))
      | ~ v1_funct_2(C_133,u1_struct_0(A_131),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_132)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_430,plain,(
    ! [B_132,C_133] :
      ( m1_subset_1('#skF_1'('#skF_3',B_132,C_133),k1_zfmisc_1(u1_struct_0(B_132)))
      | v5_pre_topc(C_133,'#skF_3',B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0(B_132))))
      | ~ v1_funct_2(C_133,u1_struct_0('#skF_3'),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_132)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_421])).

tff(c_499,plain,(
    ! [B_143,C_144] :
      ( m1_subset_1('#skF_1'('#skF_3',B_143,C_144),k1_zfmisc_1(u1_struct_0(B_143)))
      | v5_pre_topc(C_144,'#skF_3',B_143)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0(B_143))))
      | ~ v1_funct_2(C_144,k2_struct_0('#skF_3'),u1_struct_0(B_143))
      | ~ v1_funct_1(C_144)
      | ~ l1_pre_topc(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_84,c_430])).

tff(c_504,plain,(
    ! [C_144] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_4',C_144),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v5_pre_topc(C_144,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_144,k2_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_144)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_499])).

tff(c_512,plain,(
    ! [C_145] :
      ( m1_subset_1('#skF_1'('#skF_3','#skF_4',C_145),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v5_pre_topc(C_145,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_145,k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85,c_85,c_504])).

tff(c_519,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_106,c_512])).

tff(c_523,plain,
    ( m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_96,c_519])).

tff(c_524,plain,(
    m1_subset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_523])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_241,plain,(
    ! [A_91,B_92] :
      ( u1_struct_0(A_91) = B_92
      | k1_xboole_0 = B_92
      | ~ v4_pre_topc(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ v2_tdlat_3(A_91)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_251,plain,(
    ! [B_92] :
      ( u1_struct_0('#skF_4') = B_92
      | k1_xboole_0 = B_92
      | ~ v4_pre_topc(B_92,'#skF_4')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v2_tdlat_3('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_241])).

tff(c_258,plain,(
    ! [B_92] :
      ( k2_struct_0('#skF_4') = B_92
      | k1_xboole_0 = B_92
      | ~ v4_pre_topc(B_92,'#skF_4')
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_54,c_85,c_251])).

tff(c_527,plain,
    ( k2_struct_0('#skF_4') = '#skF_1'('#skF_3','#skF_4','#skF_5')
    | '#skF_1'('#skF_3','#skF_4','#skF_5') = k1_xboole_0
    | ~ v4_pre_topc('#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_524,c_258])).

tff(c_536,plain,
    ( k2_struct_0('#skF_4') = '#skF_1'('#skF_3','#skF_4','#skF_5')
    | '#skF_1'('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_527])).

tff(c_558,plain,(
    '#skF_1'('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_665,plain,(
    ! [A_171,B_172,C_173] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_171),u1_struct_0(B_172),C_173,'#skF_1'(A_171,B_172,C_173)),A_171)
      | v5_pre_topc(C_173,A_171,B_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_171),u1_struct_0(B_172))))
      | ~ v1_funct_2(C_173,u1_struct_0(A_171),u1_struct_0(B_172))
      | ~ v1_funct_1(C_173)
      | ~ l1_pre_topc(B_172)
      | ~ l1_pre_topc(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_668,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_5',k1_xboole_0),'#skF_3')
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_665])).

tff(c_682,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_52,c_50,c_96,c_84,c_85,c_106,c_84,c_85,c_238,c_116,c_154,c_84,c_85,c_668])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_682])).

tff(c_685,plain,(
    k2_struct_0('#skF_4') = '#skF_1'('#skF_3','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_703,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_96])).

tff(c_702,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_106])).

tff(c_701,plain,(
    ! [D_77] : k8_relset_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_5',D_77) = k10_relat_1('#skF_5',D_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_154])).

tff(c_540,plain,(
    ! [B_146,A_147,C_148] :
      ( k2_struct_0(B_146) = k1_xboole_0
      | k8_relset_1(u1_struct_0(A_147),u1_struct_0(B_146),C_148,k2_struct_0(B_146)) = k2_struct_0(A_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_147),u1_struct_0(B_146))))
      | ~ v1_funct_2(C_148,u1_struct_0(A_147),u1_struct_0(B_146))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0(B_146)
      | ~ l1_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_549,plain,(
    ! [B_146,C_148] :
      ( k2_struct_0(B_146) = k1_xboole_0
      | k8_relset_1(u1_struct_0('#skF_3'),u1_struct_0(B_146),C_148,k2_struct_0(B_146)) = k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0(B_146))))
      | ~ v1_funct_2(C_148,u1_struct_0('#skF_3'),u1_struct_0(B_146))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0(B_146)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_540])).

tff(c_555,plain,(
    ! [B_146,C_148] :
      ( k2_struct_0(B_146) = k1_xboole_0
      | k8_relset_1(k2_struct_0('#skF_3'),u1_struct_0(B_146),C_148,k2_struct_0(B_146)) = k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0(B_146))))
      | ~ v1_funct_2(C_148,k2_struct_0('#skF_3'),u1_struct_0(B_146))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0(B_146)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84,c_549])).

tff(c_923,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_555])).

tff(c_926,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_923])).

tff(c_930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_926])).

tff(c_932,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_555])).

tff(c_686,plain,(
    '#skF_1'('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_545,plain,(
    ! [B_146,C_148] :
      ( k2_struct_0(B_146) = k1_xboole_0
      | k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0(B_146),C_148,k2_struct_0(B_146)) = k2_struct_0('#skF_4')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_146))))
      | ~ v1_funct_2(C_148,u1_struct_0('#skF_4'),u1_struct_0(B_146))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0(B_146)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_540])).

tff(c_553,plain,(
    ! [B_146,C_148] :
      ( k2_struct_0(B_146) = k1_xboole_0
      | k8_relset_1(k2_struct_0('#skF_4'),u1_struct_0(B_146),C_148,k2_struct_0(B_146)) = k2_struct_0('#skF_4')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_146))))
      | ~ v1_funct_2(C_148,k2_struct_0('#skF_4'),u1_struct_0(B_146))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0(B_146)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_545])).

tff(c_2283,plain,(
    ! [B_146,C_148] :
      ( k2_struct_0(B_146) = k1_xboole_0
      | k8_relset_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0(B_146),C_148,k2_struct_0(B_146)) = '#skF_1'('#skF_3','#skF_4','#skF_5')
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1('#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0(B_146))))
      | ~ v1_funct_2(C_148,'#skF_1'('#skF_3','#skF_4','#skF_5'),u1_struct_0(B_146))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0(B_146)
      | ~ l1_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_685,c_685,c_685,c_553])).

tff(c_2284,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2283])).

tff(c_2287,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_2284])).

tff(c_2291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2287])).

tff(c_2293,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2283])).

tff(c_547,plain,(
    ! [A_147,C_148] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | k8_relset_1(u1_struct_0(A_147),u1_struct_0('#skF_4'),C_148,k2_struct_0('#skF_4')) = k2_struct_0(A_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_147),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_148,u1_struct_0(A_147),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_540])).

tff(c_554,plain,(
    ! [A_147,C_148] :
      ( k2_struct_0('#skF_4') = k1_xboole_0
      | k8_relset_1(u1_struct_0(A_147),k2_struct_0('#skF_4'),C_148,k2_struct_0('#skF_4')) = k2_struct_0(A_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_147),k2_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_148,u1_struct_0(A_147),k2_struct_0('#skF_4'))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0('#skF_4')
      | ~ l1_struct_0(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_85,c_547])).

tff(c_2300,plain,(
    ! [A_147,C_148] :
      ( '#skF_1'('#skF_3','#skF_4','#skF_5') = k1_xboole_0
      | k8_relset_1(u1_struct_0(A_147),'#skF_1'('#skF_3','#skF_4','#skF_5'),C_148,'#skF_1'('#skF_3','#skF_4','#skF_5')) = k2_struct_0(A_147)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_147),'#skF_1'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(C_148,u1_struct_0(A_147),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_1(C_148)
      | ~ l1_struct_0(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2293,c_685,c_685,c_685,c_685,c_685,c_554])).

tff(c_2302,plain,(
    ! [A_358,C_359] :
      ( k8_relset_1(u1_struct_0(A_358),'#skF_1'('#skF_3','#skF_4','#skF_5'),C_359,'#skF_1'('#skF_3','#skF_4','#skF_5')) = k2_struct_0(A_358)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_358),'#skF_1'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(C_359,u1_struct_0(A_358),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_1(C_359)
      | ~ l1_struct_0(A_358) ) ),
    inference(negUnitSimplification,[status(thm)],[c_686,c_2300])).

tff(c_2312,plain,(
    ! [C_359] :
      ( k8_relset_1(u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'),C_359,'#skF_1'('#skF_3','#skF_4','#skF_5')) = k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(C_359,u1_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_1(C_359)
      | ~ l1_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_2302])).

tff(c_2476,plain,(
    ! [C_383] :
      ( k8_relset_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'),C_383,'#skF_1'('#skF_3','#skF_4','#skF_5')) = k2_struct_0('#skF_3')
      | ~ m1_subset_1(C_383,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(C_383,k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_1(C_383) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_932,c_84,c_84,c_2312])).

tff(c_2479,plain,
    ( k8_relset_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'),'#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) = k2_struct_0('#skF_3')
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_702,c_2476])).

tff(c_2486,plain,(
    k10_relat_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')) = k2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_703,c_701,c_2479])).

tff(c_704,plain,(
    u1_struct_0('#skF_4') = '#skF_1'('#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_685,c_85])).

tff(c_867,plain,(
    ! [A_184,B_185,C_186] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_184),u1_struct_0(B_185),C_186,'#skF_1'(A_184,B_185,C_186)),A_184)
      | v5_pre_topc(C_186,A_184,B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184),u1_struct_0(B_185))))
      | ~ v1_funct_2(C_186,u1_struct_0(A_184),u1_struct_0(B_185))
      | ~ v1_funct_1(C_186)
      | ~ l1_pre_topc(B_185)
      | ~ l1_pre_topc(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_876,plain,(
    ! [B_185,C_186] :
      ( ~ v4_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),u1_struct_0(B_185),C_186,'#skF_1'('#skF_3',B_185,C_186)),'#skF_3')
      | v5_pre_topc(C_186,'#skF_3',B_185)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_185))))
      | ~ v1_funct_2(C_186,u1_struct_0('#skF_3'),u1_struct_0(B_185))
      | ~ v1_funct_1(C_186)
      | ~ l1_pre_topc(B_185)
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_867])).

tff(c_2339,plain,(
    ! [B_362,C_363] :
      ( ~ v4_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),u1_struct_0(B_362),C_363,'#skF_1'('#skF_3',B_362,C_363)),'#skF_3')
      | v5_pre_topc(C_363,'#skF_3',B_362)
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0(B_362))))
      | ~ v1_funct_2(C_363,k2_struct_0('#skF_3'),u1_struct_0(B_362))
      | ~ v1_funct_1(C_363)
      | ~ l1_pre_topc(B_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_84,c_84,c_876])).

tff(c_2342,plain,(
    ! [C_363] :
      ( ~ v4_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'),C_363,'#skF_1'('#skF_3','#skF_4',C_363)),'#skF_3')
      | v5_pre_topc(C_363,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(C_363,k2_struct_0('#skF_3'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(C_363)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_2339])).

tff(c_2732,plain,(
    ! [C_422] :
      ( ~ v4_pre_topc(k8_relset_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'),C_422,'#skF_1'('#skF_3','#skF_4',C_422)),'#skF_3')
      | v5_pre_topc(C_422,'#skF_3','#skF_4')
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))))
      | ~ v1_funct_2(C_422,k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
      | ~ v1_funct_1(C_422) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_704,c_704,c_2342])).

tff(c_2740,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_5','#skF_1'('#skF_3','#skF_4','#skF_5')),'#skF_3')
    | v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))))
    | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_3'),'#skF_1'('#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_701,c_2732])).

tff(c_2743,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_703,c_702,c_2486,c_2740])).

tff(c_2744,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2743])).

tff(c_2747,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_2744])).

tff(c_2751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2747])).

%------------------------------------------------------------------------------

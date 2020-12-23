%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1803+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:26 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 172 expanded)
%              Number of leaves         :   40 (  78 expanded)
%              Depth                    :   24
%              Number of atoms          :  418 ( 895 expanded)
%              Number of equality atoms :   26 (  57 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r1_tmap_1 > v1_funct_2 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k9_tmap_1 > k8_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_tmap_1,type,(
    k9_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_tmap_1,type,(
    k8_tmap_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_220,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tmap_1(B,k8_tmap_1(A,B),k2_tmap_1(A,k8_tmap_1(A,B),k9_tmap_1(A,B),B),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_tmap_1)).

tff(f_201,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B))
        & l1_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_tmap_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( v1_funct_1(k9_tmap_1(A,B))
        & v1_funct_2(k9_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
        & m1_subset_1(k9_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_tmap_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_pre_topc(B,A) )
     => ( ~ v2_struct_0(k8_tmap_1(A,B))
        & v1_pre_topc(k8_tmap_1(A,B))
        & v2_pre_topc(k8_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_pre_topc(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( C = k8_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => C = k6_tmap_1(A,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_tmap_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B))))) )
             => ( C = k9_tmap_1(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( D = u1_struct_0(B)
                     => r1_funct_2(u1_struct_0(A),u1_struct_0(k8_tmap_1(A,B)),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,D)),C,k7_tmap_1(A,D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_tmap_1)).

tff(f_171,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_194,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( u1_struct_0(C) = B
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(C))
                   => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_tmap_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_52,plain,(
    ! [B_78,A_76] :
      ( m1_subset_1(u1_struct_0(B_78),k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_24,plain,(
    ! [A_47,B_48] :
      ( l1_pre_topc(k8_tmap_1(A_47,B_48))
      | ~ m1_pre_topc(B_48,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_36,plain,(
    ! [A_51] :
      ( l1_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_34,plain,(
    ! [A_49,B_50] :
      ( v1_funct_1(k9_tmap_1(A_49,B_50))
      | ~ m1_pre_topc(B_50,A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_75,plain,(
    ! [A_97,B_98] :
      ( v1_funct_1(k7_tmap_1(A_97,B_98))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_pre_topc(A_97)
      | ~ v2_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_79,plain,(
    ! [A_76,B_78] :
      ( v1_funct_1(k7_tmap_1(A_76,u1_struct_0(B_78)))
      | ~ v2_pre_topc(A_76)
      | v2_struct_0(A_76)
      | ~ m1_pre_topc(B_78,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_32,plain,(
    ! [A_49,B_50] :
      ( v1_funct_2(k9_tmap_1(A_49,B_50),u1_struct_0(A_49),u1_struct_0(k8_tmap_1(A_49,B_50)))
      | ~ m1_pre_topc(B_50,A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    ! [A_53,B_54] :
      ( v1_pre_topc(k8_tmap_1(A_53,B_54))
      | ~ m1_pre_topc(B_54,A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    ! [A_53,B_54] :
      ( v2_pre_topc(k8_tmap_1(A_53,B_54))
      | ~ m1_pre_topc(B_54,A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_109,plain,(
    ! [A_126,B_127] :
      ( k6_tmap_1(A_126,u1_struct_0(B_127)) = k8_tmap_1(A_126,B_127)
      | ~ m1_subset_1(u1_struct_0(B_127),k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(k8_tmap_1(A_126,B_127))
      | ~ v2_pre_topc(k8_tmap_1(A_126,B_127))
      | ~ v1_pre_topc(k8_tmap_1(A_126,B_127))
      | ~ m1_pre_topc(B_127,A_126)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_115,plain,(
    ! [A_134,B_135] :
      ( k6_tmap_1(A_134,u1_struct_0(B_135)) = k8_tmap_1(A_134,B_135)
      | ~ l1_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ v2_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ v1_pre_topc(k8_tmap_1(A_134,B_135))
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134)
      | ~ m1_pre_topc(B_135,A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(resolution,[status(thm)],[c_52,c_109])).

tff(c_120,plain,(
    ! [A_136,B_137] :
      ( k6_tmap_1(A_136,u1_struct_0(B_137)) = k8_tmap_1(A_136,B_137)
      | ~ l1_pre_topc(k8_tmap_1(A_136,B_137))
      | ~ v1_pre_topc(k8_tmap_1(A_136,B_137))
      | ~ m1_pre_topc(B_137,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_125,plain,(
    ! [A_138,B_139] :
      ( k6_tmap_1(A_138,u1_struct_0(B_139)) = k8_tmap_1(A_138,B_139)
      | ~ l1_pre_topc(k8_tmap_1(A_138,B_139))
      | ~ m1_pre_topc(B_139,A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_42,c_120])).

tff(c_130,plain,(
    ! [A_140,B_141] :
      ( k6_tmap_1(A_140,u1_struct_0(B_141)) = k8_tmap_1(A_140,B_141)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_24,c_125])).

tff(c_20,plain,(
    ! [A_45,B_46] :
      ( v1_funct_2(k7_tmap_1(A_45,B_46),u1_struct_0(A_45),u1_struct_0(k6_tmap_1(A_45,B_46)))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_139,plain,(
    ! [A_140,B_141] :
      ( v1_funct_2(k7_tmap_1(A_140,u1_struct_0(B_141)),u1_struct_0(A_140),u1_struct_0(k8_tmap_1(A_140,B_141)))
      | ~ m1_subset_1(u1_struct_0(B_141),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_20])).

tff(c_30,plain,(
    ! [A_49,B_50] :
      ( m1_subset_1(k9_tmap_1(A_49,B_50),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_49),u1_struct_0(k8_tmap_1(A_49,B_50)))))
      | ~ m1_pre_topc(B_50,A_49)
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k7_tmap_1(A_45,B_46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_45),u1_struct_0(k6_tmap_1(A_45,B_46)))))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_136,plain,(
    ! [A_140,B_141] :
      ( m1_subset_1(k7_tmap_1(A_140,u1_struct_0(B_141)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_140),u1_struct_0(k8_tmap_1(A_140,B_141)))))
      | ~ m1_subset_1(u1_struct_0(B_141),k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140)
      | ~ m1_pre_topc(B_141,A_140)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_129,plain,(
    ! [A_47,B_48] :
      ( k6_tmap_1(A_47,u1_struct_0(B_48)) = k8_tmap_1(A_47,B_48)
      | ~ m1_pre_topc(B_48,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_24,c_125])).

tff(c_240,plain,(
    ! [A_184,B_185] :
      ( r1_funct_2(u1_struct_0(A_184),u1_struct_0(k8_tmap_1(A_184,B_185)),u1_struct_0(A_184),u1_struct_0(k6_tmap_1(A_184,u1_struct_0(B_185))),k9_tmap_1(A_184,B_185),k7_tmap_1(A_184,u1_struct_0(B_185)))
      | ~ m1_subset_1(u1_struct_0(B_185),k1_zfmisc_1(u1_struct_0(A_184)))
      | ~ m1_subset_1(k9_tmap_1(A_184,B_185),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_184),u1_struct_0(k8_tmap_1(A_184,B_185)))))
      | ~ v1_funct_2(k9_tmap_1(A_184,B_185),u1_struct_0(A_184),u1_struct_0(k8_tmap_1(A_184,B_185)))
      | ~ v1_funct_1(k9_tmap_1(A_184,B_185))
      | ~ m1_pre_topc(B_185,A_184)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_281,plain,(
    ! [A_207,B_208] :
      ( r1_funct_2(u1_struct_0(A_207),u1_struct_0(k8_tmap_1(A_207,B_208)),u1_struct_0(A_207),u1_struct_0(k8_tmap_1(A_207,B_208)),k9_tmap_1(A_207,B_208),k7_tmap_1(A_207,u1_struct_0(B_208)))
      | ~ m1_subset_1(u1_struct_0(B_208),k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ m1_subset_1(k9_tmap_1(A_207,B_208),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_207),u1_struct_0(k8_tmap_1(A_207,B_208)))))
      | ~ v1_funct_2(k9_tmap_1(A_207,B_208),u1_struct_0(A_207),u1_struct_0(k8_tmap_1(A_207,B_208)))
      | ~ v1_funct_1(k9_tmap_1(A_207,B_208))
      | ~ m1_pre_topc(B_208,A_207)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207)
      | ~ m1_pre_topc(B_208,A_207)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207)
      | v2_struct_0(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_240])).

tff(c_48,plain,(
    ! [B_56,E_59,C_57,A_55,F_60,D_58] :
      ( F_60 = E_59
      | ~ r1_funct_2(A_55,B_56,C_57,D_58,E_59,F_60)
      | ~ m1_subset_1(F_60,k1_zfmisc_1(k2_zfmisc_1(C_57,D_58)))
      | ~ v1_funct_2(F_60,C_57,D_58)
      | ~ v1_funct_1(F_60)
      | ~ m1_subset_1(E_59,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_2(E_59,A_55,B_56)
      | ~ v1_funct_1(E_59)
      | v1_xboole_0(D_58)
      | v1_xboole_0(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_295,plain,(
    ! [A_217,B_218] :
      ( k7_tmap_1(A_217,u1_struct_0(B_218)) = k9_tmap_1(A_217,B_218)
      | ~ m1_subset_1(k7_tmap_1(A_217,u1_struct_0(B_218)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_217),u1_struct_0(k8_tmap_1(A_217,B_218)))))
      | ~ v1_funct_2(k7_tmap_1(A_217,u1_struct_0(B_218)),u1_struct_0(A_217),u1_struct_0(k8_tmap_1(A_217,B_218)))
      | ~ v1_funct_1(k7_tmap_1(A_217,u1_struct_0(B_218)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_217,B_218)))
      | ~ m1_subset_1(u1_struct_0(B_218),k1_zfmisc_1(u1_struct_0(A_217)))
      | ~ m1_subset_1(k9_tmap_1(A_217,B_218),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_217),u1_struct_0(k8_tmap_1(A_217,B_218)))))
      | ~ v1_funct_2(k9_tmap_1(A_217,B_218),u1_struct_0(A_217),u1_struct_0(k8_tmap_1(A_217,B_218)))
      | ~ v1_funct_1(k9_tmap_1(A_217,B_218))
      | ~ m1_pre_topc(B_218,A_217)
      | ~ l1_pre_topc(A_217)
      | ~ v2_pre_topc(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_281,c_48])).

tff(c_300,plain,(
    ! [A_219,B_220] :
      ( k7_tmap_1(A_219,u1_struct_0(B_220)) = k9_tmap_1(A_219,B_220)
      | ~ v1_funct_2(k7_tmap_1(A_219,u1_struct_0(B_220)),u1_struct_0(A_219),u1_struct_0(k8_tmap_1(A_219,B_220)))
      | ~ v1_funct_1(k7_tmap_1(A_219,u1_struct_0(B_220)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_219,B_220)))
      | ~ m1_subset_1(k9_tmap_1(A_219,B_220),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_219),u1_struct_0(k8_tmap_1(A_219,B_220)))))
      | ~ v1_funct_2(k9_tmap_1(A_219,B_220),u1_struct_0(A_219),u1_struct_0(k8_tmap_1(A_219,B_220)))
      | ~ v1_funct_1(k9_tmap_1(A_219,B_220))
      | ~ m1_subset_1(u1_struct_0(B_220),k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ m1_pre_topc(B_220,A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_136,c_295])).

tff(c_305,plain,(
    ! [A_221,B_222] :
      ( k7_tmap_1(A_221,u1_struct_0(B_222)) = k9_tmap_1(A_221,B_222)
      | ~ v1_funct_2(k7_tmap_1(A_221,u1_struct_0(B_222)),u1_struct_0(A_221),u1_struct_0(k8_tmap_1(A_221,B_222)))
      | ~ v1_funct_1(k7_tmap_1(A_221,u1_struct_0(B_222)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_221,B_222)))
      | ~ v1_funct_2(k9_tmap_1(A_221,B_222),u1_struct_0(A_221),u1_struct_0(k8_tmap_1(A_221,B_222)))
      | ~ v1_funct_1(k9_tmap_1(A_221,B_222))
      | ~ m1_subset_1(u1_struct_0(B_222),k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ m1_pre_topc(B_222,A_221)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_30,c_300])).

tff(c_310,plain,(
    ! [A_223,B_224] :
      ( k7_tmap_1(A_223,u1_struct_0(B_224)) = k9_tmap_1(A_223,B_224)
      | ~ v1_funct_1(k7_tmap_1(A_223,u1_struct_0(B_224)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_223,B_224)))
      | ~ v1_funct_2(k9_tmap_1(A_223,B_224),u1_struct_0(A_223),u1_struct_0(k8_tmap_1(A_223,B_224)))
      | ~ v1_funct_1(k9_tmap_1(A_223,B_224))
      | ~ m1_subset_1(u1_struct_0(B_224),k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ m1_pre_topc(B_224,A_223)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(resolution,[status(thm)],[c_139,c_305])).

tff(c_315,plain,(
    ! [A_225,B_226] :
      ( k7_tmap_1(A_225,u1_struct_0(B_226)) = k9_tmap_1(A_225,B_226)
      | ~ v1_funct_1(k7_tmap_1(A_225,u1_struct_0(B_226)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_225,B_226)))
      | ~ v1_funct_1(k9_tmap_1(A_225,B_226))
      | ~ m1_subset_1(u1_struct_0(B_226),k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ m1_pre_topc(B_226,A_225)
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(resolution,[status(thm)],[c_32,c_310])).

tff(c_320,plain,(
    ! [A_227,B_228] :
      ( k7_tmap_1(A_227,u1_struct_0(B_228)) = k9_tmap_1(A_227,B_228)
      | ~ v1_funct_1(k7_tmap_1(A_227,u1_struct_0(B_228)))
      | v1_xboole_0(u1_struct_0(k8_tmap_1(A_227,B_228)))
      | ~ v1_funct_1(k9_tmap_1(A_227,B_228))
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227)
      | ~ m1_pre_topc(B_228,A_227)
      | ~ l1_pre_topc(A_227) ) ),
    inference(resolution,[status(thm)],[c_52,c_315])).

tff(c_38,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(u1_struct_0(A_52))
      | ~ l1_struct_0(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_325,plain,(
    ! [A_229,B_230] :
      ( ~ l1_struct_0(k8_tmap_1(A_229,B_230))
      | v2_struct_0(k8_tmap_1(A_229,B_230))
      | k7_tmap_1(A_229,u1_struct_0(B_230)) = k9_tmap_1(A_229,B_230)
      | ~ v1_funct_1(k7_tmap_1(A_229,u1_struct_0(B_230)))
      | ~ v1_funct_1(k9_tmap_1(A_229,B_230))
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229)
      | ~ m1_pre_topc(B_230,A_229)
      | ~ l1_pre_topc(A_229) ) ),
    inference(resolution,[status(thm)],[c_320,c_38])).

tff(c_337,plain,(
    ! [A_233,B_234] :
      ( ~ l1_struct_0(k8_tmap_1(A_233,B_234))
      | v2_struct_0(k8_tmap_1(A_233,B_234))
      | k7_tmap_1(A_233,u1_struct_0(B_234)) = k9_tmap_1(A_233,B_234)
      | ~ v1_funct_1(k9_tmap_1(A_233,B_234))
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233)
      | ~ m1_pre_topc(B_234,A_233)
      | ~ l1_pre_topc(A_233) ) ),
    inference(resolution,[status(thm)],[c_79,c_325])).

tff(c_44,plain,(
    ! [A_53,B_54] :
      ( ~ v2_struct_0(k8_tmap_1(A_53,B_54))
      | ~ m1_pre_topc(B_54,A_53)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_342,plain,(
    ! [A_235,B_236] :
      ( ~ l1_struct_0(k8_tmap_1(A_235,B_236))
      | k7_tmap_1(A_235,u1_struct_0(B_236)) = k9_tmap_1(A_235,B_236)
      | ~ v1_funct_1(k9_tmap_1(A_235,B_236))
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235)
      | ~ m1_pre_topc(B_236,A_235)
      | ~ l1_pre_topc(A_235) ) ),
    inference(resolution,[status(thm)],[c_337,c_44])).

tff(c_347,plain,(
    ! [A_237,B_238] :
      ( ~ l1_struct_0(k8_tmap_1(A_237,B_238))
      | k7_tmap_1(A_237,u1_struct_0(B_238)) = k9_tmap_1(A_237,B_238)
      | ~ m1_pre_topc(B_238,A_237)
      | ~ l1_pre_topc(A_237)
      | ~ v2_pre_topc(A_237)
      | v2_struct_0(A_237) ) ),
    inference(resolution,[status(thm)],[c_34,c_342])).

tff(c_352,plain,(
    ! [A_239,B_240] :
      ( k7_tmap_1(A_239,u1_struct_0(B_240)) = k9_tmap_1(A_239,B_240)
      | ~ m1_pre_topc(B_240,A_239)
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239)
      | ~ l1_pre_topc(k8_tmap_1(A_239,B_240)) ) ),
    inference(resolution,[status(thm)],[c_36,c_347])).

tff(c_357,plain,(
    ! [A_241,B_242] :
      ( k7_tmap_1(A_241,u1_struct_0(B_242)) = k9_tmap_1(A_241,B_242)
      | ~ m1_pre_topc(B_242,A_241)
      | ~ l1_pre_topc(A_241)
      | ~ v2_pre_topc(A_241)
      | v2_struct_0(A_241) ) ),
    inference(resolution,[status(thm)],[c_24,c_352])).

tff(c_146,plain,(
    ! [C_144,A_145,D_146] :
      ( r1_tmap_1(C_144,k6_tmap_1(A_145,u1_struct_0(C_144)),k2_tmap_1(A_145,k6_tmap_1(A_145,u1_struct_0(C_144)),k7_tmap_1(A_145,u1_struct_0(C_144)),C_144),D_146)
      | ~ m1_subset_1(D_146,u1_struct_0(C_144))
      | ~ m1_pre_topc(C_144,A_145)
      | v2_struct_0(C_144)
      | ~ m1_subset_1(u1_struct_0(C_144),k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_207,plain,(
    ! [B_170,A_171,D_172] :
      ( r1_tmap_1(B_170,k6_tmap_1(A_171,u1_struct_0(B_170)),k2_tmap_1(A_171,k8_tmap_1(A_171,B_170),k7_tmap_1(A_171,u1_struct_0(B_170)),B_170),D_172)
      | ~ m1_subset_1(D_172,u1_struct_0(B_170))
      | ~ m1_pre_topc(B_170,A_171)
      | v2_struct_0(B_170)
      | ~ m1_subset_1(u1_struct_0(B_170),k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171)
      | ~ m1_pre_topc(B_170,A_171)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_146])).

tff(c_210,plain,(
    ! [B_48,A_47,D_172] :
      ( r1_tmap_1(B_48,k8_tmap_1(A_47,B_48),k2_tmap_1(A_47,k8_tmap_1(A_47,B_48),k7_tmap_1(A_47,u1_struct_0(B_48)),B_48),D_172)
      | ~ m1_subset_1(D_172,u1_struct_0(B_48))
      | ~ m1_pre_topc(B_48,A_47)
      | v2_struct_0(B_48)
      | ~ m1_subset_1(u1_struct_0(B_48),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47)
      | ~ m1_pre_topc(B_48,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47)
      | ~ m1_pre_topc(B_48,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_207])).

tff(c_451,plain,(
    ! [B_260,A_261,D_262] :
      ( r1_tmap_1(B_260,k8_tmap_1(A_261,B_260),k2_tmap_1(A_261,k8_tmap_1(A_261,B_260),k9_tmap_1(A_261,B_260),B_260),D_262)
      | ~ m1_subset_1(D_262,u1_struct_0(B_260))
      | ~ m1_pre_topc(B_260,A_261)
      | v2_struct_0(B_260)
      | ~ m1_subset_1(u1_struct_0(B_260),k1_zfmisc_1(u1_struct_0(A_261)))
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261)
      | ~ m1_pre_topc(B_260,A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261)
      | ~ m1_pre_topc(B_260,A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261)
      | ~ m1_pre_topc(B_260,A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_210])).

tff(c_54,plain,(
    ~ r1_tmap_1('#skF_4',k8_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k8_tmap_1('#skF_3','#skF_4'),k9_tmap_1('#skF_3','#skF_4'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_454,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_451,c_54])).

tff(c_457,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_56,c_454])).

tff(c_458,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_60,c_457])).

tff(c_461,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_458])).

tff(c_465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_461])).

%------------------------------------------------------------------------------

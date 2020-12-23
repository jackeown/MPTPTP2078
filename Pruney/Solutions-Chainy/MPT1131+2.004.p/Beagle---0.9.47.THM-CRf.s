%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:11 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 513 expanded)
%              Number of leaves         :   32 ( 197 expanded)
%              Depth                    :   13
%              Number of atoms          :  286 (2604 expanded)
%              Number of equality atoms :    9 ( 207 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_39,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v4_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v4_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_pre_topc)).

tff(f_60,axiom,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_424,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k8_relset_1(A_137,B_138,C_139,D_140) = k10_relat_1(C_139,D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_433,plain,(
    ! [D_140] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_140) = k10_relat_1('#skF_4',D_140) ),
    inference(resolution,[status(thm)],[c_40,c_424])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_435,plain,(
    ! [A_141,B_142,D_143,C_144] :
      ( r1_tarski(k8_relset_1(A_141,B_142,D_143,C_144),A_141)
      | ~ m1_subset_1(D_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142)))
      | ~ v1_funct_1(D_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_439,plain,(
    ! [C_144] :
      ( r1_tarski(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',C_144),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_435])).

tff(c_448,plain,(
    ! [C_144] : r1_tarski(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',C_144),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_439])).

tff(c_459,plain,(
    ! [C_144] : r1_tarski(k10_relat_1('#skF_4',C_144),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_433,c_448])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    ! [B_38,A_36] :
      ( v4_pre_topc(B_38,g1_pre_topc(u1_struct_0(A_36),u1_pre_topc(A_36)))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ v4_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_61,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_60])).

tff(c_123,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_54,plain,
    ( ~ v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_62,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_125,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_62])).

tff(c_46,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_42,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_126,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k8_relset_1(A_66,B_67,C_68,D_69) = k10_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_135,plain,(
    ! [D_69] : k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_69) = k10_relat_1('#skF_4',D_69) ),
    inference(resolution,[status(thm)],[c_40,c_126])).

tff(c_354,plain,(
    ! [A_128,B_129,C_130] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_128),u1_struct_0(B_129),C_130,'#skF_1'(A_128,B_129,C_130)),A_128)
      | v5_pre_topc(C_130,A_128,B_129)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128),u1_struct_0(B_129))))
      | ~ v1_funct_2(C_130,u1_struct_0(A_128),u1_struct_0(B_129))
      | ~ v1_funct_1(C_130)
      | ~ l1_pre_topc(B_129)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_366,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_354])).

tff(c_371,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_40,c_366])).

tff(c_372,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_371])).

tff(c_281,plain,(
    ! [A_110,B_111,C_112] :
      ( v4_pre_topc('#skF_1'(A_110,B_111,C_112),B_111)
      | v5_pre_topc(C_112,A_110,B_111)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110),u1_struct_0(B_111))))
      | ~ v1_funct_2(C_112,u1_struct_0(A_110),u1_struct_0(B_111))
      | ~ v1_funct_1(C_112)
      | ~ l1_pre_topc(B_111)
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_285,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_281])).

tff(c_294,plain,
    ( v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_285])).

tff(c_295,plain,(
    v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_294])).

tff(c_318,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1('#skF_1'(A_122,B_123,C_124),k1_zfmisc_1(u1_struct_0(B_123)))
      | v5_pre_topc(C_124,A_122,B_123)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_122),u1_struct_0(B_123))))
      | ~ v1_funct_2(C_124,u1_struct_0(A_122),u1_struct_0(B_123))
      | ~ v1_funct_1(C_124)
      | ~ l1_pre_topc(B_123)
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_322,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_318])).

tff(c_331,plain,
    ( m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_322])).

tff(c_332,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_331])).

tff(c_95,plain,(
    ! [A_62] :
      ( m1_subset_1(u1_pre_topc(A_62),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_33,B_34] :
      ( l1_pre_topc(g1_pre_topc(A_33,B_34))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_105,plain,(
    ! [A_62] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_62),u1_pre_topc(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_95,c_18])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_64,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_65,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_134,plain,(
    ! [D_69] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_69) = k10_relat_1('#skF_4',D_69) ),
    inference(resolution,[status(thm)],[c_65,c_126])).

tff(c_373,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_131),u1_struct_0(B_132),C_133,D_134),A_131)
      | ~ v4_pre_topc(D_134,B_132)
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0(B_132)))
      | ~ v5_pre_topc(C_133,A_131,B_132)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131),u1_struct_0(B_132))))
      | ~ v1_funct_2(C_133,u1_struct_0(A_131),u1_struct_0(B_132))
      | ~ v1_funct_1(C_133)
      | ~ l1_pre_topc(B_132)
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_375,plain,(
    ! [D_134] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_134),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_134,'#skF_3')
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_65,c_373])).

tff(c_383,plain,(
    ! [D_134] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_134),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_134,'#skF_3')
      | ~ m1_subset_1(D_134,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_64,c_123,c_134,c_375])).

tff(c_388,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_383])).

tff(c_391,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_388])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_391])).

tff(c_398,plain,(
    ! [D_135] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_135),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v4_pre_topc(D_135,'#skF_3')
      | ~ m1_subset_1(D_135,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_383])).

tff(c_164,plain,(
    ! [A_76,B_77,D_78,C_79] :
      ( r1_tarski(k8_relset_1(A_76,B_77,D_78,C_79),A_76)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(D_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_166,plain,(
    ! [C_79] :
      ( r1_tarski(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',C_79),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_65,c_164])).

tff(c_174,plain,(
    ! [C_79] : r1_tarski(k10_relat_1('#skF_4',C_79),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_134,c_166])).

tff(c_215,plain,(
    ! [B_100,A_101] :
      ( v4_pre_topc(B_100,A_101)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_101),u1_pre_topc(A_101)))))
      | ~ v4_pre_topc(B_100,g1_pre_topc(u1_struct_0(A_101),u1_pre_topc(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_225,plain,(
    ! [A_102,A_103] :
      ( v4_pre_topc(A_102,A_103)
      | ~ v4_pre_topc(A_102,g1_pre_topc(u1_struct_0(A_103),u1_pre_topc(A_103)))
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | ~ r1_tarski(A_102,u1_struct_0(g1_pre_topc(u1_struct_0(A_103),u1_pre_topc(A_103)))) ) ),
    inference(resolution,[status(thm)],[c_4,c_215])).

tff(c_235,plain,(
    ! [C_79] :
      ( v4_pre_topc(k10_relat_1('#skF_4',C_79),'#skF_2')
      | ~ v4_pre_topc(k10_relat_1('#skF_4',C_79),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_174,c_225])).

tff(c_240,plain,(
    ! [C_79] :
      ( v4_pre_topc(k10_relat_1('#skF_4',C_79),'#skF_2')
      | ~ v4_pre_topc(k10_relat_1('#skF_4',C_79),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_235])).

tff(c_407,plain,(
    ! [D_136] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_136),'#skF_2')
      | ~ v4_pre_topc(D_136,'#skF_3')
      | ~ m1_subset_1(D_136,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_398,c_240])).

tff(c_410,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_332,c_407])).

tff(c_417,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_410])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_417])).

tff(c_421,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_581,plain,(
    ! [A_181,B_182,C_183] :
      ( v4_pre_topc('#skF_1'(A_181,B_182,C_183),B_182)
      | v5_pre_topc(C_183,A_181,B_182)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181),u1_struct_0(B_182))))
      | ~ v1_funct_2(C_183,u1_struct_0(A_181),u1_struct_0(B_182))
      | ~ v1_funct_1(C_183)
      | ~ l1_pre_topc(B_182)
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_583,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_65,c_581])).

tff(c_591,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_64,c_583])).

tff(c_592,plain,
    ( v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_591])).

tff(c_597,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_592])).

tff(c_600,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_105,c_597])).

tff(c_604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_600])).

tff(c_606,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_432,plain,(
    ! [D_140] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'),'#skF_4',D_140) = k10_relat_1('#skF_4',D_140) ),
    inference(resolution,[status(thm)],[c_65,c_424])).

tff(c_648,plain,(
    ! [A_196,B_197,C_198] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(A_196),u1_struct_0(B_197),C_198,'#skF_1'(A_196,B_197,C_198)),A_196)
      | v5_pre_topc(C_198,A_196,B_197)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_196),u1_struct_0(B_197))))
      | ~ v1_funct_2(C_198,u1_struct_0(A_196),u1_struct_0(B_197))
      | ~ v1_funct_1(C_198)
      | ~ l1_pre_topc(B_197)
      | ~ l1_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_656,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_648])).

tff(c_663,plain,
    ( ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_46,c_44,c_64,c_65,c_656])).

tff(c_664,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_663])).

tff(c_669,plain,
    ( ~ m1_subset_1(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_664])).

tff(c_672,plain,
    ( ~ m1_subset_1(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_669])).

tff(c_673,plain,(
    ~ v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_672])).

tff(c_605,plain,(
    v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_592])).

tff(c_628,plain,(
    ! [A_193,B_194,C_195] :
      ( m1_subset_1('#skF_1'(A_193,B_194,C_195),k1_zfmisc_1(u1_struct_0(B_194)))
      | v5_pre_topc(C_195,A_193,B_194)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193),u1_struct_0(B_194))))
      | ~ v1_funct_2(C_195,u1_struct_0(A_193),u1_struct_0(B_194))
      | ~ v1_funct_1(C_195)
      | ~ l1_pre_topc(B_194)
      | ~ l1_pre_topc(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_630,plain,
    ( m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_65,c_628])).

tff(c_638,plain,
    ( m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_46,c_44,c_64,c_630])).

tff(c_639,plain,(
    m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_638])).

tff(c_420,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_674,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_199),u1_struct_0(B_200),C_201,D_202),A_199)
      | ~ v4_pre_topc(D_202,B_200)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0(B_200)))
      | ~ v5_pre_topc(C_201,A_199,B_200)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,u1_struct_0(A_199),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ l1_pre_topc(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_678,plain,(
    ! [D_202] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'),'#skF_4',D_202),'#skF_2')
      | ~ v4_pre_topc(D_202,'#skF_3')
      | ~ m1_subset_1(D_202,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_674])).

tff(c_689,plain,(
    ! [D_203] :
      ( v4_pre_topc(k10_relat_1('#skF_4',D_203),'#skF_2')
      | ~ v4_pre_topc(D_203,'#skF_3')
      | ~ m1_subset_1(D_203,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_44,c_42,c_420,c_433,c_678])).

tff(c_692,plain,
    ( v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2')
    | ~ v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_639,c_689])).

tff(c_699,plain,(
    v4_pre_topc(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_692])).

tff(c_701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_673,c_699])).

tff(c_702,plain,(
    ~ m1_subset_1(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_672])).

tff(c_706,plain,(
    ~ r1_tarski(k10_relat_1('#skF_4','#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_702])).

tff(c_710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.45  
% 3.19/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.45  %$ v5_pre_topc > v1_funct_2 > v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > k10_relat_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.19/1.45  
% 3.19/1.45  %Foreground sorts:
% 3.19/1.45  
% 3.19/1.45  
% 3.19/1.45  %Background operators:
% 3.19/1.45  
% 3.19/1.45  
% 3.19/1.45  %Foreground operators:
% 3.19/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.19/1.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.19/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.19/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.19/1.45  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.19/1.45  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.19/1.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.19/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.19/1.45  tff('#skF_5', type, '#skF_5': $i).
% 3.19/1.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.19/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.19/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.19/1.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.19/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.19/1.45  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.19/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.19/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.19/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.19/1.45  tff('#skF_4', type, '#skF_4': $i).
% 3.19/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.19/1.45  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 3.19/1.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.19/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.19/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.19/1.45  
% 3.19/1.48  tff(f_113, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 3.19/1.48  tff(f_33, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.19/1.48  tff(f_39, axiom, (![A, B, C, D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r1_tarski(k8_relset_1(A, B, D, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_2)).
% 3.19/1.48  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.19/1.48  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v4_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v4_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_pre_topc)).
% 3.19/1.48  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (v5_pre_topc(C, A, B) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(D, B) => v4_pre_topc(k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, D), A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_pre_topc)).
% 3.19/1.48  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.19/1.48  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 3.19/1.48  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_424, plain, (![A_137, B_138, C_139, D_140]: (k8_relset_1(A_137, B_138, C_139, D_140)=k10_relat_1(C_139, D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.48  tff(c_433, plain, (![D_140]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_140)=k10_relat_1('#skF_4', D_140))), inference(resolution, [status(thm)], [c_40, c_424])).
% 3.19/1.48  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_435, plain, (![A_141, B_142, D_143, C_144]: (r1_tarski(k8_relset_1(A_141, B_142, D_143, C_144), A_141) | ~m1_subset_1(D_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))) | ~v1_funct_1(D_143))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.48  tff(c_439, plain, (![C_144]: (r1_tarski(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', C_144), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_435])).
% 3.19/1.48  tff(c_448, plain, (![C_144]: (r1_tarski(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', C_144), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_439])).
% 3.19/1.48  tff(c_459, plain, (![C_144]: (r1_tarski(k10_relat_1('#skF_4', C_144), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_433, c_448])).
% 3.19/1.48  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.19/1.48  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_26, plain, (![B_38, A_36]: (v4_pre_topc(B_38, g1_pre_topc(u1_struct_0(A_36), u1_pre_topc(A_36))) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_36))) | ~v4_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.19/1.48  tff(c_32, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_60, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_5', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_61, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_60])).
% 3.19/1.48  tff(c_123, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_61])).
% 3.19/1.48  tff(c_54, plain, (~v5_pre_topc('#skF_5', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_62, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_54])).
% 3.19/1.48  tff(c_125, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_62])).
% 3.19/1.48  tff(c_46, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_42, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_126, plain, (![A_66, B_67, C_68, D_69]: (k8_relset_1(A_66, B_67, C_68, D_69)=k10_relat_1(C_68, D_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.19/1.48  tff(c_135, plain, (![D_69]: (k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_69)=k10_relat_1('#skF_4', D_69))), inference(resolution, [status(thm)], [c_40, c_126])).
% 3.19/1.48  tff(c_354, plain, (![A_128, B_129, C_130]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_128), u1_struct_0(B_129), C_130, '#skF_1'(A_128, B_129, C_130)), A_128) | v5_pre_topc(C_130, A_128, B_129) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_128), u1_struct_0(B_129)))) | ~v1_funct_2(C_130, u1_struct_0(A_128), u1_struct_0(B_129)) | ~v1_funct_1(C_130) | ~l1_pre_topc(B_129) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_366, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135, c_354])).
% 3.19/1.48  tff(c_371, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_42, c_40, c_366])).
% 3.19/1.48  tff(c_372, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_125, c_371])).
% 3.19/1.48  tff(c_281, plain, (![A_110, B_111, C_112]: (v4_pre_topc('#skF_1'(A_110, B_111, C_112), B_111) | v5_pre_topc(C_112, A_110, B_111) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_110), u1_struct_0(B_111)))) | ~v1_funct_2(C_112, u1_struct_0(A_110), u1_struct_0(B_111)) | ~v1_funct_1(C_112) | ~l1_pre_topc(B_111) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_285, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_281])).
% 3.19/1.48  tff(c_294, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_42, c_285])).
% 3.19/1.48  tff(c_295, plain, (v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_125, c_294])).
% 3.19/1.48  tff(c_318, plain, (![A_122, B_123, C_124]: (m1_subset_1('#skF_1'(A_122, B_123, C_124), k1_zfmisc_1(u1_struct_0(B_123))) | v5_pre_topc(C_124, A_122, B_123) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_122), u1_struct_0(B_123)))) | ~v1_funct_2(C_124, u1_struct_0(A_122), u1_struct_0(B_123)) | ~v1_funct_1(C_124) | ~l1_pre_topc(B_123) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_322, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_318])).
% 3.19/1.48  tff(c_331, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_42, c_322])).
% 3.19/1.48  tff(c_332, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_125, c_331])).
% 3.19/1.48  tff(c_95, plain, (![A_62]: (m1_subset_1(u1_pre_topc(A_62), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.19/1.48  tff(c_18, plain, (![A_33, B_34]: (l1_pre_topc(g1_pre_topc(A_33, B_34)) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.19/1.48  tff(c_105, plain, (![A_62]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_62), u1_pre_topc(A_62))) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_95, c_18])).
% 3.19/1.48  tff(c_36, plain, (v1_funct_2('#skF_5', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_64, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_36])).
% 3.19/1.48  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.19/1.48  tff(c_65, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.19/1.48  tff(c_134, plain, (![D_69]: (k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', D_69)=k10_relat_1('#skF_4', D_69))), inference(resolution, [status(thm)], [c_65, c_126])).
% 3.19/1.48  tff(c_373, plain, (![A_131, B_132, C_133, D_134]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_131), u1_struct_0(B_132), C_133, D_134), A_131) | ~v4_pre_topc(D_134, B_132) | ~m1_subset_1(D_134, k1_zfmisc_1(u1_struct_0(B_132))) | ~v5_pre_topc(C_133, A_131, B_132) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_131), u1_struct_0(B_132)))) | ~v1_funct_2(C_133, u1_struct_0(A_131), u1_struct_0(B_132)) | ~v1_funct_1(C_133) | ~l1_pre_topc(B_132) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_375, plain, (![D_134]: (v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', D_134), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v4_pre_topc(D_134, '#skF_3') | ~m1_subset_1(D_134, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_65, c_373])).
% 3.19/1.48  tff(c_383, plain, (![D_134]: (v4_pre_topc(k10_relat_1('#skF_4', D_134), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v4_pre_topc(D_134, '#skF_3') | ~m1_subset_1(D_134, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_64, c_123, c_134, c_375])).
% 3.19/1.48  tff(c_388, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_383])).
% 3.19/1.48  tff(c_391, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_105, c_388])).
% 3.19/1.48  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_391])).
% 3.19/1.48  tff(c_398, plain, (![D_135]: (v4_pre_topc(k10_relat_1('#skF_4', D_135), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v4_pre_topc(D_135, '#skF_3') | ~m1_subset_1(D_135, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_383])).
% 3.19/1.48  tff(c_164, plain, (![A_76, B_77, D_78, C_79]: (r1_tarski(k8_relset_1(A_76, B_77, D_78, C_79), A_76) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(D_78))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.19/1.48  tff(c_166, plain, (![C_79]: (r1_tarski(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', C_79), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_65, c_164])).
% 3.19/1.48  tff(c_174, plain, (![C_79]: (r1_tarski(k10_relat_1('#skF_4', C_79), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_134, c_166])).
% 3.19/1.48  tff(c_215, plain, (![B_100, A_101]: (v4_pre_topc(B_100, A_101) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_101), u1_pre_topc(A_101))))) | ~v4_pre_topc(B_100, g1_pre_topc(u1_struct_0(A_101), u1_pre_topc(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.19/1.48  tff(c_225, plain, (![A_102, A_103]: (v4_pre_topc(A_102, A_103) | ~v4_pre_topc(A_102, g1_pre_topc(u1_struct_0(A_103), u1_pre_topc(A_103))) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | ~r1_tarski(A_102, u1_struct_0(g1_pre_topc(u1_struct_0(A_103), u1_pre_topc(A_103)))))), inference(resolution, [status(thm)], [c_4, c_215])).
% 3.19/1.48  tff(c_235, plain, (![C_79]: (v4_pre_topc(k10_relat_1('#skF_4', C_79), '#skF_2') | ~v4_pre_topc(k10_relat_1('#skF_4', C_79), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_174, c_225])).
% 3.19/1.48  tff(c_240, plain, (![C_79]: (v4_pre_topc(k10_relat_1('#skF_4', C_79), '#skF_2') | ~v4_pre_topc(k10_relat_1('#skF_4', C_79), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_235])).
% 3.19/1.48  tff(c_407, plain, (![D_136]: (v4_pre_topc(k10_relat_1('#skF_4', D_136), '#skF_2') | ~v4_pre_topc(D_136, '#skF_3') | ~m1_subset_1(D_136, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_398, c_240])).
% 3.19/1.48  tff(c_410, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2') | ~v4_pre_topc('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_332, c_407])).
% 3.19/1.48  tff(c_417, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_410])).
% 3.19/1.48  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_372, c_417])).
% 3.19/1.48  tff(c_421, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_61])).
% 3.19/1.48  tff(c_581, plain, (![A_181, B_182, C_183]: (v4_pre_topc('#skF_1'(A_181, B_182, C_183), B_182) | v5_pre_topc(C_183, A_181, B_182) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_181), u1_struct_0(B_182)))) | ~v1_funct_2(C_183, u1_struct_0(A_181), u1_struct_0(B_182)) | ~v1_funct_1(C_183) | ~l1_pre_topc(B_182) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_583, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_65, c_581])).
% 3.19/1.48  tff(c_591, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_64, c_583])).
% 3.19/1.48  tff(c_592, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_421, c_591])).
% 3.19/1.48  tff(c_597, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_592])).
% 3.19/1.48  tff(c_600, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_105, c_597])).
% 3.19/1.48  tff(c_604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_600])).
% 3.19/1.48  tff(c_606, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_592])).
% 3.19/1.48  tff(c_432, plain, (![D_140]: (k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'), '#skF_4', D_140)=k10_relat_1('#skF_4', D_140))), inference(resolution, [status(thm)], [c_65, c_424])).
% 3.19/1.48  tff(c_648, plain, (![A_196, B_197, C_198]: (~v4_pre_topc(k8_relset_1(u1_struct_0(A_196), u1_struct_0(B_197), C_198, '#skF_1'(A_196, B_197, C_198)), A_196) | v5_pre_topc(C_198, A_196, B_197) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_196), u1_struct_0(B_197)))) | ~v1_funct_2(C_198, u1_struct_0(A_196), u1_struct_0(B_197)) | ~v1_funct_1(C_198) | ~l1_pre_topc(B_197) | ~l1_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_656, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_432, c_648])).
% 3.19/1.48  tff(c_663, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_606, c_46, c_44, c_64, c_65, c_656])).
% 3.19/1.48  tff(c_664, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_421, c_663])).
% 3.19/1.48  tff(c_669, plain, (~m1_subset_1(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_664])).
% 3.19/1.48  tff(c_672, plain, (~m1_subset_1(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_669])).
% 3.19/1.48  tff(c_673, plain, (~v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2')), inference(splitLeft, [status(thm)], [c_672])).
% 3.19/1.48  tff(c_605, plain, (v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_592])).
% 3.19/1.48  tff(c_628, plain, (![A_193, B_194, C_195]: (m1_subset_1('#skF_1'(A_193, B_194, C_195), k1_zfmisc_1(u1_struct_0(B_194))) | v5_pre_topc(C_195, A_193, B_194) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_193), u1_struct_0(B_194)))) | ~v1_funct_2(C_195, u1_struct_0(A_193), u1_struct_0(B_194)) | ~v1_funct_1(C_195) | ~l1_pre_topc(B_194) | ~l1_pre_topc(A_193))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_630, plain, (m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_65, c_628])).
% 3.19/1.48  tff(c_638, plain, (m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_606, c_46, c_44, c_64, c_630])).
% 3.19/1.48  tff(c_639, plain, (m1_subset_1('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_421, c_638])).
% 3.19/1.48  tff(c_420, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_61])).
% 3.19/1.48  tff(c_674, plain, (![A_199, B_200, C_201, D_202]: (v4_pre_topc(k8_relset_1(u1_struct_0(A_199), u1_struct_0(B_200), C_201, D_202), A_199) | ~v4_pre_topc(D_202, B_200) | ~m1_subset_1(D_202, k1_zfmisc_1(u1_struct_0(B_200))) | ~v5_pre_topc(C_201, A_199, B_200) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, u1_struct_0(A_199), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_pre_topc(B_200) | ~l1_pre_topc(A_199))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.19/1.48  tff(c_678, plain, (![D_202]: (v4_pre_topc(k8_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'), '#skF_4', D_202), '#skF_2') | ~v4_pre_topc(D_202, '#skF_3') | ~m1_subset_1(D_202, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_674])).
% 3.19/1.48  tff(c_689, plain, (![D_203]: (v4_pre_topc(k10_relat_1('#skF_4', D_203), '#skF_2') | ~v4_pre_topc(D_203, '#skF_3') | ~m1_subset_1(D_203, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_44, c_42, c_420, c_433, c_678])).
% 3.19/1.48  tff(c_692, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2') | ~v4_pre_topc('#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_639, c_689])).
% 3.19/1.48  tff(c_699, plain, (v4_pre_topc(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_692])).
% 3.19/1.48  tff(c_701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_673, c_699])).
% 3.19/1.48  tff(c_702, plain, (~m1_subset_1(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_672])).
% 3.19/1.48  tff(c_706, plain, (~r1_tarski(k10_relat_1('#skF_4', '#skF_1'(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_702])).
% 3.19/1.48  tff(c_710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_459, c_706])).
% 3.19/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.48  
% 3.19/1.48  Inference rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Ref     : 0
% 3.19/1.48  #Sup     : 119
% 3.19/1.48  #Fact    : 0
% 3.19/1.48  #Define  : 0
% 3.19/1.48  #Split   : 4
% 3.19/1.48  #Chain   : 0
% 3.19/1.48  #Close   : 0
% 3.19/1.48  
% 3.19/1.48  Ordering : KBO
% 3.19/1.48  
% 3.19/1.48  Simplification rules
% 3.19/1.48  ----------------------
% 3.19/1.48  #Subsume      : 5
% 3.19/1.48  #Demod        : 158
% 3.19/1.48  #Tautology    : 46
% 3.19/1.48  #SimpNegUnit  : 11
% 3.19/1.48  #BackRed      : 0
% 3.19/1.48  
% 3.19/1.48  #Partial instantiations: 0
% 3.19/1.48  #Strategies tried      : 1
% 3.19/1.48  
% 3.19/1.48  Timing (in seconds)
% 3.19/1.48  ----------------------
% 3.34/1.48  Preprocessing        : 0.33
% 3.34/1.48  Parsing              : 0.17
% 3.34/1.48  CNF conversion       : 0.03
% 3.34/1.48  Main loop            : 0.37
% 3.34/1.48  Inferencing          : 0.14
% 3.34/1.48  Reduction            : 0.12
% 3.34/1.48  Demodulation         : 0.08
% 3.34/1.48  BG Simplification    : 0.02
% 3.34/1.48  Subsumption          : 0.06
% 3.34/1.48  Abstraction          : 0.02
% 3.34/1.48  MUC search           : 0.00
% 3.34/1.48  Cooper               : 0.00
% 3.34/1.48  Total                : 0.75
% 3.34/1.48  Index Insertion      : 0.00
% 3.34/1.48  Index Deletion       : 0.00
% 3.34/1.48  Index Matching       : 0.00
% 3.34/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

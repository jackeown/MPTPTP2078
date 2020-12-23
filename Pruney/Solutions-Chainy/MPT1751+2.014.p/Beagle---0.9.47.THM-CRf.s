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
% DateTime   : Thu Dec  3 10:26:59 EST 2020

% Result     : Theorem 5.23s
% Output     : CNFRefutation 5.23s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 293 expanded)
%              Number of leaves         :   41 ( 129 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 (1429 expanded)
%              Number of equality atoms :   36 ( 151 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ! [E] :
                        ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                       => ( r1_tarski(E,u1_struct_0(C))
                         => k7_relset_1(u1_struct_0(B),u1_struct_0(A),D,E) = k7_relset_1(u1_struct_0(C),u1_struct_0(A),k2_tmap_1(B,A,D,C),E) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tmap_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_59,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_36,c_59])).

tff(c_68,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_38,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_146,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k2_partfun1(A_112,B_113,C_114,D_115) = k7_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_150,plain,(
    ! [D_115] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_115) = k7_relat_1('#skF_4',D_115)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_36,c_146])).

tff(c_154,plain,(
    ! [D_115] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_115) = k7_relat_1('#skF_4',D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_150])).

tff(c_233,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k2_partfun1(u1_struct_0(A_130),u1_struct_0(B_131),C_132,u1_struct_0(D_133)) = k2_tmap_1(A_130,B_131,C_132,D_133)
      | ~ m1_pre_topc(D_133,A_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130),u1_struct_0(B_131))))
      | ~ v1_funct_2(C_132,u1_struct_0(A_130),u1_struct_0(B_131))
      | ~ v1_funct_1(C_132)
      | ~ l1_pre_topc(B_131)
      | ~ v2_pre_topc(B_131)
      | v2_struct_0(B_131)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_243,plain,(
    ! [D_133] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_133)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_133)
      | ~ m1_pre_topc(D_133,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_36,c_233])).

tff(c_252,plain,(
    ! [D_133] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_133)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_133)
      | ~ m1_pre_topc(D_133,'#skF_2')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_54,c_52,c_40,c_38,c_154,c_243])).

tff(c_255,plain,(
    ! [D_136] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_136)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_136)
      | ~ m1_pre_topc(D_136,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_252])).

tff(c_10,plain,(
    ! [A_8,C_12,B_11] :
      ( k9_relat_1(k7_relat_1(A_8,C_12),B_11) = k9_relat_1(A_8,B_11)
      | ~ r1_tarski(B_11,C_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_278,plain,(
    ! [D_136,B_11] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_136),B_11) = k9_relat_1('#skF_4',B_11)
      | ~ r1_tarski(B_11,u1_struct_0(D_136))
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc(D_136,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_10])).

tff(c_584,plain,(
    ! [D_207,B_208] :
      ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_207),B_208) = k9_relat_1('#skF_4',B_208)
      | ~ r1_tarski(B_208,u1_struct_0(D_207))
      | ~ m1_pre_topc(D_207,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_278])).

tff(c_598,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_584])).

tff(c_604,plain,(
    k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') = k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_598])).

tff(c_167,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( m1_subset_1(k2_partfun1(A_121,B_122,C_123,D_124),k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_185,plain,(
    ! [D_115] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_115),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_167])).

tff(c_195,plain,(
    ! [D_115] : m1_subset_1(k7_relat_1('#skF_4',D_115),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_185])).

tff(c_525,plain,(
    ! [D_200] :
      ( m1_subset_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_200),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))))
      | ~ m1_pre_topc(D_200,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_195])).

tff(c_18,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k7_relset_1(A_18,B_19,C_20,D_21) = k9_relat_1(C_20,D_21)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1174,plain,(
    ! [D_370,D_371] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_370),D_371) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_370),D_371)
      | ~ m1_pre_topc(D_370,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_525,c_18])).

tff(c_253,plain,(
    ! [D_133] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_133)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_133)
      | ~ m1_pre_topc(D_133,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_56,c_252])).

tff(c_196,plain,(
    ! [D_125] : m1_subset_1(k7_relat_1('#skF_4',D_125),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_185])).

tff(c_481,plain,(
    ! [D_188,D_189] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_188),D_189) = k9_relat_1(k7_relat_1('#skF_4',D_188),D_189) ),
    inference(resolution,[status(thm)],[c_196,c_18])).

tff(c_490,plain,(
    ! [D_133,D_189] :
      ( k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_133),D_189) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_133)),D_189)
      | ~ m1_pre_topc(D_133,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_481])).

tff(c_1180,plain,(
    ! [D_370,D_371] :
      ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_370)),D_371) = k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4',D_370),D_371)
      | ~ m1_pre_topc(D_370,'#skF_2')
      | ~ m1_pre_topc(D_370,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1174,c_490])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v1_relat_1(B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_211,plain,(
    ! [D_125] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_125))
      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_223,plain,(
    ! [D_125] : v1_relat_1(k7_relat_1('#skF_4',D_125)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_211])).

tff(c_14,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_220,plain,(
    ! [D_125] : v5_relat_1(k7_relat_1('#skF_4',D_125),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_196,c_14])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [C_103,A_104,B_105] :
      ( m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ r1_tarski(k2_relat_1(C_103),B_105)
      | ~ r1_tarski(k1_relat_1(C_103),A_104)
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_649,plain,(
    ! [A_214,B_215,C_216,D_217] :
      ( k7_relset_1(A_214,B_215,C_216,D_217) = k9_relat_1(C_216,D_217)
      | ~ r1_tarski(k2_relat_1(C_216),B_215)
      | ~ r1_tarski(k1_relat_1(C_216),A_214)
      | ~ v1_relat_1(C_216) ) ),
    inference(resolution,[status(thm)],[c_117,c_18])).

tff(c_653,plain,(
    ! [A_218,A_219,B_220,D_221] :
      ( k7_relset_1(A_218,A_219,B_220,D_221) = k9_relat_1(B_220,D_221)
      | ~ r1_tarski(k1_relat_1(B_220),A_218)
      | ~ v5_relat_1(B_220,A_219)
      | ~ v1_relat_1(B_220) ) ),
    inference(resolution,[status(thm)],[c_6,c_649])).

tff(c_1971,plain,(
    ! [A_507,A_508,B_509,D_510] :
      ( k7_relset_1(A_507,A_508,k7_relat_1(B_509,A_507),D_510) = k9_relat_1(k7_relat_1(B_509,A_507),D_510)
      | ~ v5_relat_1(k7_relat_1(B_509,A_507),A_508)
      | ~ v1_relat_1(k7_relat_1(B_509,A_507))
      | ~ v1_relat_1(B_509) ) ),
    inference(resolution,[status(thm)],[c_12,c_653])).

tff(c_1987,plain,(
    ! [D_125,D_510] :
      ( k7_relset_1(D_125,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_125),D_510) = k9_relat_1(k7_relat_1('#skF_4',D_125),D_510)
      | ~ v1_relat_1(k7_relat_1('#skF_4',D_125))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_220,c_1971])).

tff(c_2005,plain,(
    ! [D_511,D_512] : k7_relset_1(D_511,u1_struct_0('#skF_1'),k7_relat_1('#skF_4',D_511),D_512) = k9_relat_1(k7_relat_1('#skF_4',D_511),D_512) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_223,c_1987])).

tff(c_2049,plain,(
    ! [D_516,D_517] :
      ( k7_relset_1(u1_struct_0(D_516),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4',D_516),D_517) = k9_relat_1(k7_relat_1('#skF_4',u1_struct_0(D_516)),D_517)
      | ~ m1_pre_topc(D_516,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_2005])).

tff(c_103,plain,(
    ! [A_98,B_99,C_100,D_101] :
      ( k7_relset_1(A_98,B_99,C_100,D_101) = k9_relat_1(C_100,D_101)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_106,plain,(
    ! [D_101] : k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_101) = k9_relat_1('#skF_4',D_101) ),
    inference(resolution,[status(thm)],[c_36,c_103])).

tff(c_30,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k7_relset_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_107,plain,(
    k7_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_30])).

tff(c_2063,plain,
    ( k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2049,c_107])).

tff(c_2078,plain,(
    k9_relat_1(k7_relat_1('#skF_4',u1_struct_0('#skF_3')),'#skF_5') != k9_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2063])).

tff(c_2130,plain,
    ( k9_relat_1(k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_5') != k9_relat_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1180,c_2078])).

tff(c_2139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_604,c_2130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.23/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/1.95  
% 5.23/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/1.95  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_relat_1 > v1_funct_1 > l1_pre_topc > k7_relset_1 > k2_tmap_1 > k2_partfun1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.23/1.95  
% 5.23/1.95  %Foreground sorts:
% 5.23/1.95  
% 5.23/1.95  
% 5.23/1.95  %Background operators:
% 5.23/1.95  
% 5.23/1.95  
% 5.23/1.95  %Foreground operators:
% 5.23/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.23/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.23/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.23/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.23/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.23/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.23/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.23/1.95  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.23/1.95  tff('#skF_5', type, '#skF_5': $i).
% 5.23/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.23/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.23/1.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.23/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.23/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.23/1.95  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.23/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.23/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.23/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.23/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.23/1.95  tff('#skF_4', type, '#skF_4': $i).
% 5.23/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.23/1.95  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.23/1.95  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.23/1.95  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.23/1.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.23/1.95  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.23/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.23/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.23/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.23/1.95  
% 5.23/1.97  tff(f_146, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (r1_tarski(E, u1_struct_0(C)) => (k7_relset_1(u1_struct_0(B), u1_struct_0(A), D, E) = k7_relset_1(u1_struct_0(C), u1_struct_0(A), k2_tmap_1(B, A, D, C), E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_tmap_1)).
% 5.23/1.97  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.23/1.97  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.23/1.97  tff(f_83, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.23/1.97  tff(f_110, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.23/1.97  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 5.23/1.97  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 5.23/1.97  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.23/1.97  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.23/1.97  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 5.23/1.97  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.23/1.97  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.23/1.97  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_32, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.23/1.97  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_59, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.23/1.97  tff(c_62, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_59])).
% 5.23/1.97  tff(c_68, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_62])).
% 5.23/1.97  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_38, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_146, plain, (![A_112, B_113, C_114, D_115]: (k2_partfun1(A_112, B_113, C_114, D_115)=k7_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_1(C_114))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.23/1.97  tff(c_150, plain, (![D_115]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_115)=k7_relat_1('#skF_4', D_115) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_36, c_146])).
% 5.23/1.97  tff(c_154, plain, (![D_115]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_115)=k7_relat_1('#skF_4', D_115))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_150])).
% 5.23/1.97  tff(c_233, plain, (![A_130, B_131, C_132, D_133]: (k2_partfun1(u1_struct_0(A_130), u1_struct_0(B_131), C_132, u1_struct_0(D_133))=k2_tmap_1(A_130, B_131, C_132, D_133) | ~m1_pre_topc(D_133, A_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_130), u1_struct_0(B_131)))) | ~v1_funct_2(C_132, u1_struct_0(A_130), u1_struct_0(B_131)) | ~v1_funct_1(C_132) | ~l1_pre_topc(B_131) | ~v2_pre_topc(B_131) | v2_struct_0(B_131) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.23/1.97  tff(c_243, plain, (![D_133]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_133))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_133) | ~m1_pre_topc(D_133, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_233])).
% 5.23/1.97  tff(c_252, plain, (![D_133]: (k7_relat_1('#skF_4', u1_struct_0(D_133))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_133) | ~m1_pre_topc(D_133, '#skF_2') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_54, c_52, c_40, c_38, c_154, c_243])).
% 5.23/1.97  tff(c_255, plain, (![D_136]: (k7_relat_1('#skF_4', u1_struct_0(D_136))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_136) | ~m1_pre_topc(D_136, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_252])).
% 5.23/1.97  tff(c_10, plain, (![A_8, C_12, B_11]: (k9_relat_1(k7_relat_1(A_8, C_12), B_11)=k9_relat_1(A_8, B_11) | ~r1_tarski(B_11, C_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.23/1.97  tff(c_278, plain, (![D_136, B_11]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_136), B_11)=k9_relat_1('#skF_4', B_11) | ~r1_tarski(B_11, u1_struct_0(D_136)) | ~v1_relat_1('#skF_4') | ~m1_pre_topc(D_136, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_10])).
% 5.23/1.97  tff(c_584, plain, (![D_207, B_208]: (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_207), B_208)=k9_relat_1('#skF_4', B_208) | ~r1_tarski(B_208, u1_struct_0(D_207)) | ~m1_pre_topc(D_207, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_278])).
% 5.23/1.97  tff(c_598, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_584])).
% 5.23/1.97  tff(c_604, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_598])).
% 5.23/1.97  tff(c_167, plain, (![A_121, B_122, C_123, D_124]: (m1_subset_1(k2_partfun1(A_121, B_122, C_123, D_124), k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_1(C_123))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.23/1.97  tff(c_185, plain, (![D_115]: (m1_subset_1(k7_relat_1('#skF_4', D_115), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_167])).
% 5.23/1.97  tff(c_195, plain, (![D_115]: (m1_subset_1(k7_relat_1('#skF_4', D_115), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_185])).
% 5.23/1.97  tff(c_525, plain, (![D_200]: (m1_subset_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_200), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))) | ~m1_pre_topc(D_200, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_195])).
% 5.23/1.97  tff(c_18, plain, (![A_18, B_19, C_20, D_21]: (k7_relset_1(A_18, B_19, C_20, D_21)=k9_relat_1(C_20, D_21) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.23/1.97  tff(c_1174, plain, (![D_370, D_371]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_370), D_371)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_370), D_371) | ~m1_pre_topc(D_370, '#skF_2'))), inference(resolution, [status(thm)], [c_525, c_18])).
% 5.23/1.97  tff(c_253, plain, (![D_133]: (k7_relat_1('#skF_4', u1_struct_0(D_133))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_133) | ~m1_pre_topc(D_133, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_50, c_56, c_252])).
% 5.23/1.97  tff(c_196, plain, (![D_125]: (m1_subset_1(k7_relat_1('#skF_4', D_125), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_185])).
% 5.23/1.97  tff(c_481, plain, (![D_188, D_189]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_188), D_189)=k9_relat_1(k7_relat_1('#skF_4', D_188), D_189))), inference(resolution, [status(thm)], [c_196, c_18])).
% 5.23/1.97  tff(c_490, plain, (![D_133, D_189]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_133), D_189)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_133)), D_189) | ~m1_pre_topc(D_133, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_481])).
% 5.23/1.97  tff(c_1180, plain, (![D_370, D_371]: (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_370)), D_371)=k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_370), D_371) | ~m1_pre_topc(D_370, '#skF_2') | ~m1_pre_topc(D_370, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1174, c_490])).
% 5.23/1.97  tff(c_2, plain, (![B_3, A_1]: (v1_relat_1(B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.23/1.97  tff(c_211, plain, (![D_125]: (v1_relat_1(k7_relat_1('#skF_4', D_125)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_196, c_2])).
% 5.23/1.97  tff(c_223, plain, (![D_125]: (v1_relat_1(k7_relat_1('#skF_4', D_125)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_211])).
% 5.23/1.97  tff(c_14, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.23/1.97  tff(c_220, plain, (![D_125]: (v5_relat_1(k7_relat_1('#skF_4', D_125), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_196, c_14])).
% 5.23/1.97  tff(c_12, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.23/1.97  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.23/1.97  tff(c_117, plain, (![C_103, A_104, B_105]: (m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~r1_tarski(k2_relat_1(C_103), B_105) | ~r1_tarski(k1_relat_1(C_103), A_104) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.23/1.97  tff(c_649, plain, (![A_214, B_215, C_216, D_217]: (k7_relset_1(A_214, B_215, C_216, D_217)=k9_relat_1(C_216, D_217) | ~r1_tarski(k2_relat_1(C_216), B_215) | ~r1_tarski(k1_relat_1(C_216), A_214) | ~v1_relat_1(C_216))), inference(resolution, [status(thm)], [c_117, c_18])).
% 5.23/1.97  tff(c_653, plain, (![A_218, A_219, B_220, D_221]: (k7_relset_1(A_218, A_219, B_220, D_221)=k9_relat_1(B_220, D_221) | ~r1_tarski(k1_relat_1(B_220), A_218) | ~v5_relat_1(B_220, A_219) | ~v1_relat_1(B_220))), inference(resolution, [status(thm)], [c_6, c_649])).
% 5.23/1.97  tff(c_1971, plain, (![A_507, A_508, B_509, D_510]: (k7_relset_1(A_507, A_508, k7_relat_1(B_509, A_507), D_510)=k9_relat_1(k7_relat_1(B_509, A_507), D_510) | ~v5_relat_1(k7_relat_1(B_509, A_507), A_508) | ~v1_relat_1(k7_relat_1(B_509, A_507)) | ~v1_relat_1(B_509))), inference(resolution, [status(thm)], [c_12, c_653])).
% 5.23/1.97  tff(c_1987, plain, (![D_125, D_510]: (k7_relset_1(D_125, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_125), D_510)=k9_relat_1(k7_relat_1('#skF_4', D_125), D_510) | ~v1_relat_1(k7_relat_1('#skF_4', D_125)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_220, c_1971])).
% 5.23/1.97  tff(c_2005, plain, (![D_511, D_512]: (k7_relset_1(D_511, u1_struct_0('#skF_1'), k7_relat_1('#skF_4', D_511), D_512)=k9_relat_1(k7_relat_1('#skF_4', D_511), D_512))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_223, c_1987])).
% 5.23/1.97  tff(c_2049, plain, (![D_516, D_517]: (k7_relset_1(u1_struct_0(D_516), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_516), D_517)=k9_relat_1(k7_relat_1('#skF_4', u1_struct_0(D_516)), D_517) | ~m1_pre_topc(D_516, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_2005])).
% 5.23/1.97  tff(c_103, plain, (![A_98, B_99, C_100, D_101]: (k7_relset_1(A_98, B_99, C_100, D_101)=k9_relat_1(C_100, D_101) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.23/1.97  tff(c_106, plain, (![D_101]: (k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_101)=k9_relat_1('#skF_4', D_101))), inference(resolution, [status(thm)], [c_36, c_103])).
% 5.23/1.97  tff(c_30, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k7_relset_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.23/1.97  tff(c_107, plain, (k7_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_30])).
% 5.23/1.97  tff(c_2063, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2049, c_107])).
% 5.23/1.97  tff(c_2078, plain, (k9_relat_1(k7_relat_1('#skF_4', u1_struct_0('#skF_3')), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2063])).
% 5.23/1.97  tff(c_2130, plain, (k9_relat_1(k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_5')!=k9_relat_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1180, c_2078])).
% 5.23/1.97  tff(c_2139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_604, c_2130])).
% 5.23/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.23/1.97  
% 5.23/1.97  Inference rules
% 5.23/1.97  ----------------------
% 5.23/1.97  #Ref     : 0
% 5.23/1.97  #Sup     : 473
% 5.23/1.97  #Fact    : 0
% 5.23/1.97  #Define  : 0
% 5.23/1.97  #Split   : 1
% 5.23/1.97  #Chain   : 0
% 5.23/1.97  #Close   : 0
% 5.23/1.97  
% 5.23/1.97  Ordering : KBO
% 5.23/1.97  
% 5.23/1.97  Simplification rules
% 5.23/1.97  ----------------------
% 5.23/1.97  #Subsume      : 28
% 5.23/1.97  #Demod        : 609
% 5.23/1.97  #Tautology    : 125
% 5.23/1.97  #SimpNegUnit  : 60
% 5.23/1.97  #BackRed      : 16
% 5.23/1.97  
% 5.23/1.97  #Partial instantiations: 0
% 5.23/1.97  #Strategies tried      : 1
% 5.23/1.97  
% 5.23/1.97  Timing (in seconds)
% 5.23/1.97  ----------------------
% 5.23/1.98  Preprocessing        : 0.34
% 5.23/1.98  Parsing              : 0.18
% 5.23/1.98  CNF conversion       : 0.03
% 5.23/1.98  Main loop            : 0.88
% 5.23/1.98  Inferencing          : 0.32
% 5.23/1.98  Reduction            : 0.33
% 5.23/1.98  Demodulation         : 0.24
% 5.23/1.98  BG Simplification    : 0.04
% 5.23/1.98  Subsumption          : 0.13
% 5.23/1.98  Abstraction          : 0.05
% 5.23/1.98  MUC search           : 0.00
% 5.23/1.98  Cooper               : 0.00
% 5.23/1.98  Total                : 1.25
% 5.23/1.98  Index Insertion      : 0.00
% 5.23/1.98  Index Deletion       : 0.00
% 5.23/1.98  Index Matching       : 0.00
% 5.23/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------

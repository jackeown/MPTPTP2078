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
% DateTime   : Thu Dec  3 10:27:54 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 389 expanded)
%              Number of leaves         :   39 ( 163 expanded)
%              Depth                    :   16
%              Number of atoms          :  329 (1748 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_233,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( r1_xboole_0(u1_struct_0(C),B)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(C))
                     => r1_tmap_1(C,k6_tmap_1(A,B),k2_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_169,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ~ r2_hidden(C,B)
               => r1_tmap_1(A,k6_tmap_1(A,B),k7_tmap_1(A,B),C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_151,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_209,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_48,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_379,plain,(
    ! [C_198,A_199,B_200] :
      ( m1_subset_1(C_198,u1_struct_0(A_199))
      | ~ m1_subset_1(C_198,u1_struct_0(B_200))
      | ~ m1_pre_topc(B_200,A_199)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_381,plain,(
    ! [A_199] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_199))
      | ~ m1_pre_topc('#skF_4',A_199)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(resolution,[status(thm)],[c_44,c_379])).

tff(c_384,plain,(
    ! [A_199] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_199))
      | ~ m1_pre_topc('#skF_4',A_199)
      | ~ l1_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_381])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_68,plain,(
    ! [B_121,A_122] :
      ( v2_pre_topc(B_121)
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_68])).

tff(c_74,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_71])).

tff(c_59,plain,(
    ! [B_115,A_116] :
      ( l1_pre_topc(B_115)
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_65,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_62])).

tff(c_18,plain,(
    ! [B_27,A_25] :
      ( r2_hidden(B_27,k1_connsp_2(A_25,B_27))
      | ~ m1_subset_1(B_27,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_389,plain,(
    ! [A_202,B_203] :
      ( m1_subset_1(k1_connsp_2(A_202,B_203),k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ m1_subset_1(B_203,u1_struct_0(A_202))
      | ~ l1_pre_topc(A_202)
      | ~ v2_pre_topc(A_202)
      | v2_struct_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [C_127,A_128,B_129] :
      ( r2_hidden(C_127,A_128)
      | ~ r2_hidden(C_127,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_158,plain,(
    ! [A_140,B_141,A_142] :
      ( r2_hidden('#skF_1'(A_140,B_141),A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_142))
      | r1_xboole_0(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_4,c_90])).

tff(c_46,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_75,plain,(
    ! [A_123,B_124,C_125] :
      ( ~ r1_xboole_0(A_123,B_124)
      | ~ r2_hidden(C_125,B_124)
      | ~ r2_hidden(C_125,A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [C_125] :
      ( ~ r2_hidden(C_125,'#skF_3')
      | ~ r2_hidden(C_125,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_46,c_75])).

tff(c_214,plain,(
    ! [A_153,B_154] :
      ( ~ r2_hidden('#skF_1'(A_153,B_154),'#skF_3')
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_xboole_0(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_158,c_78])).

tff(c_229,plain,(
    ! [B_2] :
      ( ~ m1_subset_1(B_2,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | r1_xboole_0('#skF_3',B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_214])).

tff(c_412,plain,(
    ! [B_203] :
      ( r1_xboole_0('#skF_3',k1_connsp_2('#skF_4',B_203))
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_389,c_229])).

tff(c_444,plain,(
    ! [B_203] :
      ( r1_xboole_0('#skF_3',k1_connsp_2('#skF_4',B_203))
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_65,c_412])).

tff(c_461,plain,(
    ! [B_206] :
      ( r1_xboole_0('#skF_3',k1_connsp_2('#skF_4',B_206))
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_444])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_469,plain,(
    ! [C_208,B_209] :
      ( ~ r2_hidden(C_208,k1_connsp_2('#skF_4',B_209))
      | ~ r2_hidden(C_208,'#skF_3')
      | ~ m1_subset_1(B_209,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_461,c_2])).

tff(c_473,plain,(
    ! [B_27] :
      ( ~ r2_hidden(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_469])).

tff(c_492,plain,(
    ! [B_27] :
      ( ~ r2_hidden(B_27,'#skF_3')
      | ~ m1_subset_1(B_27,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_65,c_473])).

tff(c_498,plain,(
    ! [B_210] :
      ( ~ r2_hidden(B_210,'#skF_3')
      | ~ m1_subset_1(B_210,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_492])).

tff(c_510,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_498])).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_38,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_tmap_1(A_34,k6_tmap_1(A_34,B_38),k7_tmap_1(A_34,B_38),C_40)
      | r2_hidden(C_40,B_38)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_28,plain,(
    ! [A_30,B_31] :
      ( v1_funct_2(k7_tmap_1(A_30,B_31),u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_301,plain,(
    ! [A_174,B_175] :
      ( ~ v2_struct_0(k6_tmap_1(A_174,B_175))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(u1_struct_0(A_174)))
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_304,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_301])).

tff(c_307,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_304])).

tff(c_308,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_307])).

tff(c_137,plain,(
    ! [A_136,B_137] :
      ( v2_pre_topc(k6_tmap_1(A_136,B_137))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136)
      | ~ v2_pre_topc(A_136)
      | v2_struct_0(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_140,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_137])).

tff(c_143,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_140])).

tff(c_144,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_143])).

tff(c_257,plain,(
    ! [A_164,B_165] :
      ( l1_pre_topc(k6_tmap_1(A_164,B_165))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_260,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_257])).

tff(c_263,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_260])).

tff(c_264,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_263])).

tff(c_309,plain,(
    ! [A_176,B_177] :
      ( v1_funct_1(k7_tmap_1(A_176,B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_312,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_309])).

tff(c_315,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_312])).

tff(c_316,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_315])).

tff(c_26,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k7_tmap_1(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_662,plain,(
    ! [F_264,D_266,A_262,C_265,B_263] :
      ( r1_tmap_1(D_266,A_262,k2_tmap_1(B_263,A_262,C_265,D_266),F_264)
      | ~ r1_tmap_1(B_263,A_262,C_265,F_264)
      | ~ m1_subset_1(F_264,u1_struct_0(D_266))
      | ~ m1_subset_1(F_264,u1_struct_0(B_263))
      | ~ m1_pre_topc(D_266,B_263)
      | v2_struct_0(D_266)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263),u1_struct_0(A_262))))
      | ~ v1_funct_2(C_265,u1_struct_0(B_263),u1_struct_0(A_262))
      | ~ v1_funct_1(C_265)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | v2_struct_0(A_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_804,plain,(
    ! [D_307,A_308,B_309,F_310] :
      ( r1_tmap_1(D_307,k6_tmap_1(A_308,B_309),k2_tmap_1(A_308,k6_tmap_1(A_308,B_309),k7_tmap_1(A_308,B_309),D_307),F_310)
      | ~ r1_tmap_1(A_308,k6_tmap_1(A_308,B_309),k7_tmap_1(A_308,B_309),F_310)
      | ~ m1_subset_1(F_310,u1_struct_0(D_307))
      | ~ m1_subset_1(F_310,u1_struct_0(A_308))
      | ~ m1_pre_topc(D_307,A_308)
      | v2_struct_0(D_307)
      | ~ v1_funct_2(k7_tmap_1(A_308,B_309),u1_struct_0(A_308),u1_struct_0(k6_tmap_1(A_308,B_309)))
      | ~ v1_funct_1(k7_tmap_1(A_308,B_309))
      | ~ l1_pre_topc(k6_tmap_1(A_308,B_309))
      | ~ v2_pre_topc(k6_tmap_1(A_308,B_309))
      | v2_struct_0(k6_tmap_1(A_308,B_309))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_26,c_662])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_2','#skF_3'),k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_233])).

tff(c_807,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | ~ v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_804,c_42])).

tff(c_810,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_144,c_264,c_316,c_48,c_44,c_807])).

tff(c_811,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_308,c_50,c_810])).

tff(c_831,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_834,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_831])).

tff(c_837,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_834])).

tff(c_839,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_837])).

tff(c_840,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_842,plain,(
    ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_840])).

tff(c_845,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_842])).

tff(c_848,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_845])).

tff(c_849,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_510,c_848])).

tff(c_852,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_384,c_849])).

tff(c_855,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_852])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_855])).

tff(c_858,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_840])).

tff(c_862,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_384,c_858])).

tff(c_865,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_862])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_865])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.59  
% 3.79/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.59  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.79/1.59  
% 3.79/1.59  %Foreground sorts:
% 3.79/1.59  
% 3.79/1.59  
% 3.79/1.59  %Background operators:
% 3.79/1.59  
% 3.79/1.59  
% 3.79/1.59  %Foreground operators:
% 3.79/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.79/1.59  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 3.79/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.79/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.79/1.59  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 3.79/1.59  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.79/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.79/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.79/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.79/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.79/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.79/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.79/1.59  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.79/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.79/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.79/1.59  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.79/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.79/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.79/1.59  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.79/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.79/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.79/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.59  
% 3.79/1.61  tff(f_233, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 3.79/1.61  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 3.79/1.61  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.79/1.61  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.79/1.61  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 3.79/1.61  tff(f_93, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 3.79/1.61  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.79/1.61  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.79/1.61  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 3.79/1.61  tff(f_135, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 3.79/1.61  tff(f_151, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 3.79/1.61  tff(f_120, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.79/1.61  tff(f_209, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.79/1.61  tff(c_58, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_48, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_44, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_379, plain, (![C_198, A_199, B_200]: (m1_subset_1(C_198, u1_struct_0(A_199)) | ~m1_subset_1(C_198, u1_struct_0(B_200)) | ~m1_pre_topc(B_200, A_199) | v2_struct_0(B_200) | ~l1_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.79/1.61  tff(c_381, plain, (![A_199]: (m1_subset_1('#skF_5', u1_struct_0(A_199)) | ~m1_pre_topc('#skF_4', A_199) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_199) | v2_struct_0(A_199))), inference(resolution, [status(thm)], [c_44, c_379])).
% 3.79/1.61  tff(c_384, plain, (![A_199]: (m1_subset_1('#skF_5', u1_struct_0(A_199)) | ~m1_pre_topc('#skF_4', A_199) | ~l1_pre_topc(A_199) | v2_struct_0(A_199))), inference(negUnitSimplification, [status(thm)], [c_50, c_381])).
% 3.79/1.61  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_68, plain, (![B_121, A_122]: (v2_pre_topc(B_121) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.79/1.61  tff(c_71, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_68])).
% 3.79/1.61  tff(c_74, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_71])).
% 3.79/1.61  tff(c_59, plain, (![B_115, A_116]: (l1_pre_topc(B_115) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.79/1.61  tff(c_62, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_59])).
% 3.79/1.61  tff(c_65, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_62])).
% 3.79/1.61  tff(c_18, plain, (![B_27, A_25]: (r2_hidden(B_27, k1_connsp_2(A_25, B_27)) | ~m1_subset_1(B_27, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.79/1.61  tff(c_389, plain, (![A_202, B_203]: (m1_subset_1(k1_connsp_2(A_202, B_203), k1_zfmisc_1(u1_struct_0(A_202))) | ~m1_subset_1(B_203, u1_struct_0(A_202)) | ~l1_pre_topc(A_202) | ~v2_pre_topc(A_202) | v2_struct_0(A_202))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/1.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.61  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.61  tff(c_90, plain, (![C_127, A_128, B_129]: (r2_hidden(C_127, A_128) | ~r2_hidden(C_127, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.79/1.61  tff(c_158, plain, (![A_140, B_141, A_142]: (r2_hidden('#skF_1'(A_140, B_141), A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(A_142)) | r1_xboole_0(A_140, B_141))), inference(resolution, [status(thm)], [c_4, c_90])).
% 3.79/1.61  tff(c_46, plain, (r1_xboole_0(u1_struct_0('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_75, plain, (![A_123, B_124, C_125]: (~r1_xboole_0(A_123, B_124) | ~r2_hidden(C_125, B_124) | ~r2_hidden(C_125, A_123))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.61  tff(c_78, plain, (![C_125]: (~r2_hidden(C_125, '#skF_3') | ~r2_hidden(C_125, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_46, c_75])).
% 3.79/1.61  tff(c_214, plain, (![A_153, B_154]: (~r2_hidden('#skF_1'(A_153, B_154), '#skF_3') | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0('#skF_4'))) | r1_xboole_0(A_153, B_154))), inference(resolution, [status(thm)], [c_158, c_78])).
% 3.79/1.61  tff(c_229, plain, (![B_2]: (~m1_subset_1(B_2, k1_zfmisc_1(u1_struct_0('#skF_4'))) | r1_xboole_0('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_214])).
% 3.79/1.61  tff(c_412, plain, (![B_203]: (r1_xboole_0('#skF_3', k1_connsp_2('#skF_4', B_203)) | ~m1_subset_1(B_203, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_389, c_229])).
% 3.79/1.61  tff(c_444, plain, (![B_203]: (r1_xboole_0('#skF_3', k1_connsp_2('#skF_4', B_203)) | ~m1_subset_1(B_203, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_65, c_412])).
% 3.79/1.61  tff(c_461, plain, (![B_206]: (r1_xboole_0('#skF_3', k1_connsp_2('#skF_4', B_206)) | ~m1_subset_1(B_206, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_444])).
% 3.79/1.61  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.79/1.61  tff(c_469, plain, (![C_208, B_209]: (~r2_hidden(C_208, k1_connsp_2('#skF_4', B_209)) | ~r2_hidden(C_208, '#skF_3') | ~m1_subset_1(B_209, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_461, c_2])).
% 3.79/1.61  tff(c_473, plain, (![B_27]: (~r2_hidden(B_27, '#skF_3') | ~m1_subset_1(B_27, u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_469])).
% 3.79/1.61  tff(c_492, plain, (![B_27]: (~r2_hidden(B_27, '#skF_3') | ~m1_subset_1(B_27, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_65, c_473])).
% 3.79/1.61  tff(c_498, plain, (![B_210]: (~r2_hidden(B_210, '#skF_3') | ~m1_subset_1(B_210, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_492])).
% 3.79/1.61  tff(c_510, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_498])).
% 3.79/1.61  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_38, plain, (![A_34, B_38, C_40]: (r1_tmap_1(A_34, k6_tmap_1(A_34, B_38), k7_tmap_1(A_34, B_38), C_40) | r2_hidden(C_40, B_38) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.79/1.61  tff(c_28, plain, (![A_30, B_31]: (v1_funct_2(k7_tmap_1(A_30, B_31), u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.79/1.61  tff(c_301, plain, (![A_174, B_175]: (~v2_struct_0(k6_tmap_1(A_174, B_175)) | ~m1_subset_1(B_175, k1_zfmisc_1(u1_struct_0(A_174))) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.79/1.61  tff(c_304, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_301])).
% 3.79/1.61  tff(c_307, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_304])).
% 3.79/1.61  tff(c_308, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_307])).
% 3.79/1.61  tff(c_137, plain, (![A_136, B_137]: (v2_pre_topc(k6_tmap_1(A_136, B_137)) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136) | ~v2_pre_topc(A_136) | v2_struct_0(A_136))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.79/1.61  tff(c_140, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_137])).
% 3.79/1.61  tff(c_143, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_140])).
% 3.79/1.61  tff(c_144, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_143])).
% 3.79/1.61  tff(c_257, plain, (![A_164, B_165]: (l1_pre_topc(k6_tmap_1(A_164, B_165)) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.79/1.61  tff(c_260, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_257])).
% 3.79/1.61  tff(c_263, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_260])).
% 3.79/1.61  tff(c_264, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_263])).
% 3.79/1.61  tff(c_309, plain, (![A_176, B_177]: (v1_funct_1(k7_tmap_1(A_176, B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.79/1.61  tff(c_312, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_52, c_309])).
% 3.79/1.61  tff(c_315, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_312])).
% 3.79/1.61  tff(c_316, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_58, c_315])).
% 3.79/1.61  tff(c_26, plain, (![A_30, B_31]: (m1_subset_1(k7_tmap_1(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_135])).
% 3.79/1.61  tff(c_662, plain, (![F_264, D_266, A_262, C_265, B_263]: (r1_tmap_1(D_266, A_262, k2_tmap_1(B_263, A_262, C_265, D_266), F_264) | ~r1_tmap_1(B_263, A_262, C_265, F_264) | ~m1_subset_1(F_264, u1_struct_0(D_266)) | ~m1_subset_1(F_264, u1_struct_0(B_263)) | ~m1_pre_topc(D_266, B_263) | v2_struct_0(D_266) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263), u1_struct_0(A_262)))) | ~v1_funct_2(C_265, u1_struct_0(B_263), u1_struct_0(A_262)) | ~v1_funct_1(C_265) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc(A_262) | ~v2_pre_topc(A_262) | v2_struct_0(A_262))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.79/1.61  tff(c_804, plain, (![D_307, A_308, B_309, F_310]: (r1_tmap_1(D_307, k6_tmap_1(A_308, B_309), k2_tmap_1(A_308, k6_tmap_1(A_308, B_309), k7_tmap_1(A_308, B_309), D_307), F_310) | ~r1_tmap_1(A_308, k6_tmap_1(A_308, B_309), k7_tmap_1(A_308, B_309), F_310) | ~m1_subset_1(F_310, u1_struct_0(D_307)) | ~m1_subset_1(F_310, u1_struct_0(A_308)) | ~m1_pre_topc(D_307, A_308) | v2_struct_0(D_307) | ~v1_funct_2(k7_tmap_1(A_308, B_309), u1_struct_0(A_308), u1_struct_0(k6_tmap_1(A_308, B_309))) | ~v1_funct_1(k7_tmap_1(A_308, B_309)) | ~l1_pre_topc(k6_tmap_1(A_308, B_309)) | ~v2_pre_topc(k6_tmap_1(A_308, B_309)) | v2_struct_0(k6_tmap_1(A_308, B_309)) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_308))) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308) | v2_struct_0(A_308))), inference(resolution, [status(thm)], [c_26, c_662])).
% 3.79/1.61  tff(c_42, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_2', '#skF_3'), k2_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_233])).
% 3.79/1.61  tff(c_807, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_804, c_42])).
% 3.79/1.61  tff(c_810, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_144, c_264, c_316, c_48, c_44, c_807])).
% 3.79/1.61  tff(c_811, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_308, c_50, c_810])).
% 3.79/1.61  tff(c_831, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_811])).
% 3.79/1.61  tff(c_834, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_831])).
% 3.79/1.61  tff(c_837, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_834])).
% 3.79/1.61  tff(c_839, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_837])).
% 3.79/1.61  tff(c_840, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_811])).
% 3.79/1.61  tff(c_842, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_840])).
% 3.79/1.61  tff(c_845, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_38, c_842])).
% 3.79/1.61  tff(c_848, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_845])).
% 3.79/1.61  tff(c_849, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_510, c_848])).
% 3.79/1.61  tff(c_852, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_384, c_849])).
% 3.79/1.61  tff(c_855, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_852])).
% 3.79/1.61  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_855])).
% 3.79/1.61  tff(c_858, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_840])).
% 3.79/1.61  tff(c_862, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_384, c_858])).
% 3.79/1.61  tff(c_865, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_862])).
% 3.79/1.61  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_865])).
% 3.79/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.79/1.61  
% 3.79/1.61  Inference rules
% 3.79/1.61  ----------------------
% 3.79/1.61  #Ref     : 0
% 3.79/1.61  #Sup     : 157
% 3.79/1.61  #Fact    : 0
% 3.79/1.61  #Define  : 0
% 3.79/1.61  #Split   : 7
% 3.79/1.61  #Chain   : 0
% 3.79/1.61  #Close   : 0
% 3.79/1.61  
% 3.79/1.61  Ordering : KBO
% 3.79/1.61  
% 3.79/1.61  Simplification rules
% 3.79/1.61  ----------------------
% 3.79/1.61  #Subsume      : 46
% 3.79/1.61  #Demod        : 59
% 3.79/1.61  #Tautology    : 1
% 3.79/1.61  #SimpNegUnit  : 25
% 3.79/1.61  #BackRed      : 0
% 3.79/1.61  
% 3.79/1.61  #Partial instantiations: 0
% 3.79/1.61  #Strategies tried      : 1
% 3.79/1.61  
% 3.79/1.61  Timing (in seconds)
% 3.79/1.61  ----------------------
% 3.79/1.62  Preprocessing        : 0.36
% 3.79/1.62  Parsing              : 0.20
% 3.79/1.62  CNF conversion       : 0.04
% 3.79/1.62  Main loop            : 0.50
% 3.79/1.62  Inferencing          : 0.18
% 3.79/1.62  Reduction            : 0.12
% 3.79/1.62  Demodulation         : 0.08
% 3.79/1.62  BG Simplification    : 0.02
% 3.79/1.62  Subsumption          : 0.15
% 3.79/1.62  Abstraction          : 0.02
% 3.79/1.62  MUC search           : 0.00
% 3.79/1.62  Cooper               : 0.00
% 3.79/1.62  Total                : 0.90
% 3.79/1.62  Index Insertion      : 0.00
% 3.79/1.62  Index Deletion       : 0.00
% 3.79/1.62  Index Matching       : 0.00
% 3.79/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

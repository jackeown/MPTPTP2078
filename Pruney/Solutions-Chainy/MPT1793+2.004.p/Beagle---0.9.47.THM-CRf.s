%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:54 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 396 expanded)
%              Number of leaves         :   42 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  315 (1753 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_237,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_92,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_47,axiom,(
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

tff(f_173,axiom,(
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

tff(f_139,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_213,axiom,(
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

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_92,plain,(
    ! [B_128,A_129] :
      ( v2_pre_topc(B_128)
      | ~ m1_pre_topc(B_128,A_129)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_95,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_98,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_95])).

tff(c_75,plain,(
    ! [B_117,A_118] :
      ( l1_pre_topc(B_117)
      | ~ m1_pre_topc(B_117,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_75])).

tff(c_81,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_78])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_230,plain,(
    ! [C_156,A_157,B_158] :
      ( m1_subset_1(C_156,u1_struct_0(A_157))
      | ~ m1_subset_1(C_156,u1_struct_0(B_158))
      | ~ m1_pre_topc(B_158,A_157)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_232,plain,(
    ! [A_157] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_157))
      | ~ m1_pre_topc('#skF_5',A_157)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_52,c_230])).

tff(c_235,plain,(
    ! [A_157] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_157))
      | ~ m1_pre_topc('#skF_5',A_157)
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_232])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    r1_xboole_0(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_99,plain,(
    ! [A_130,B_131,C_132] :
      ( ~ r1_xboole_0(A_130,B_131)
      | ~ r2_hidden(C_132,B_131)
      | ~ r2_hidden(C_132,A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [C_133] :
      ( ~ r2_hidden(C_133,'#skF_4')
      | ~ r2_hidden(C_133,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_54,c_99])).

tff(c_119,plain,(
    ! [A_11] :
      ( ~ r2_hidden(A_11,'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_11,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_147,plain,(
    ! [A_138] :
      ( ~ r2_hidden(A_138,'#skF_4')
      | ~ m1_subset_1(A_138,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_151,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_147])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_46,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_tmap_1(A_34,k6_tmap_1(A_34,B_38),k7_tmap_1(A_34,B_38),C_40)
      | r2_hidden(C_40,B_38)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( v1_funct_2(k7_tmap_1(A_30,B_31),u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_178,plain,(
    ! [A_144,B_145] :
      ( ~ v2_struct_0(k6_tmap_1(A_144,B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_184,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_178])).

tff(c_188,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_184])).

tff(c_189,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_188])).

tff(c_162,plain,(
    ! [A_140,B_141] :
      ( v2_pre_topc(k6_tmap_1(A_140,B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_168,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_162])).

tff(c_172,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_168])).

tff(c_173,plain,(
    v2_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_172])).

tff(c_191,plain,(
    ! [A_147,B_148] :
      ( l1_pre_topc(k6_tmap_1(A_147,B_148))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_197,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_191])).

tff(c_201,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_197])).

tff(c_202,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_201])).

tff(c_204,plain,(
    ! [A_150,B_151] :
      ( v1_funct_1(k7_tmap_1(A_150,B_151))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_210,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_204])).

tff(c_214,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_210])).

tff(c_215,plain,(
    v1_funct_1(k7_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_214])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k7_tmap_1(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_264,plain,(
    ! [B_172,F_173,A_171,D_175,C_174] :
      ( r1_tmap_1(D_175,A_171,k2_tmap_1(B_172,A_171,C_174,D_175),F_173)
      | ~ r1_tmap_1(B_172,A_171,C_174,F_173)
      | ~ m1_subset_1(F_173,u1_struct_0(D_175))
      | ~ m1_subset_1(F_173,u1_struct_0(B_172))
      | ~ m1_pre_topc(D_175,B_172)
      | v2_struct_0(D_175)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_172),u1_struct_0(A_171))))
      | ~ v1_funct_2(C_174,u1_struct_0(B_172),u1_struct_0(A_171))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_172)
      | ~ v2_pre_topc(B_172)
      | v2_struct_0(B_172)
      | ~ l1_pre_topc(A_171)
      | ~ v2_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_268,plain,(
    ! [D_176,A_177,B_178,F_179] :
      ( r1_tmap_1(D_176,k6_tmap_1(A_177,B_178),k2_tmap_1(A_177,k6_tmap_1(A_177,B_178),k7_tmap_1(A_177,B_178),D_176),F_179)
      | ~ r1_tmap_1(A_177,k6_tmap_1(A_177,B_178),k7_tmap_1(A_177,B_178),F_179)
      | ~ m1_subset_1(F_179,u1_struct_0(D_176))
      | ~ m1_subset_1(F_179,u1_struct_0(A_177))
      | ~ m1_pre_topc(D_176,A_177)
      | v2_struct_0(D_176)
      | ~ v1_funct_2(k7_tmap_1(A_177,B_178),u1_struct_0(A_177),u1_struct_0(k6_tmap_1(A_177,B_178)))
      | ~ v1_funct_1(k7_tmap_1(A_177,B_178))
      | ~ l1_pre_topc(k6_tmap_1(A_177,B_178))
      | ~ v2_pre_topc(k6_tmap_1(A_177,B_178))
      | v2_struct_0(k6_tmap_1(A_177,B_178))
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177)
      | ~ v2_pre_topc(A_177)
      | v2_struct_0(A_177) ) ),
    inference(resolution,[status(thm)],[c_34,c_264])).

tff(c_50,plain,(
    ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_271,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4')))
    | ~ v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_268,c_50])).

tff(c_274,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_5')
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_173,c_202,c_215,c_56,c_52,c_271])).

tff(c_275,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_189,c_58,c_274])).

tff(c_276,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_275])).

tff(c_279,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_276])).

tff(c_282,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_279])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_282])).

tff(c_285,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_275])).

tff(c_287,plain,(
    ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_285])).

tff(c_290,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_287])).

tff(c_293,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_290])).

tff(c_294,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_151,c_293])).

tff(c_297,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_294])).

tff(c_300,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_297])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_300])).

tff(c_303,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_285])).

tff(c_307,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_303])).

tff(c_310,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_307])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_310])).

tff(c_313,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_325,plain,(
    ! [A_181] :
      ( m1_subset_1('#skF_2'(A_181),k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_343,plain,(
    ! [A_185] :
      ( v1_xboole_0('#skF_2'(A_185))
      | ~ v1_xboole_0(u1_struct_0(A_185))
      | ~ l1_pre_topc(A_185)
      | ~ v2_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_325,c_10])).

tff(c_346,plain,
    ( v1_xboole_0('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_313,c_343])).

tff(c_349,plain,
    ( v1_xboole_0('#skF_2'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_81,c_346])).

tff(c_350,plain,(
    v1_xboole_0('#skF_2'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_349])).

tff(c_24,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0('#skF_2'(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_353,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_350,c_24])).

tff(c_356,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_81,c_353])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:29:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  %$ r1_tmap_1 > v1_funct_2 > v4_pre_topc > v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.82/1.39  
% 2.82/1.39  %Foreground sorts:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Background operators:
% 2.82/1.39  
% 2.82/1.39  
% 2.82/1.39  %Foreground operators:
% 2.82/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.82/1.39  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 2.82/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.39  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.82/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.82/1.39  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.82/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.82/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.82/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.82/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.39  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.82/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.39  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.39  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.82/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.39  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.82/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.82/1.39  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.82/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.82/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.82/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.39  
% 2.82/1.42  tff(f_237, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 2.82/1.42  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.82/1.42  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.82/1.42  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 2.82/1.42  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.82/1.42  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.82/1.42  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 2.82/1.42  tff(f_139, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 2.82/1.42  tff(f_155, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 2.82/1.42  tff(f_124, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.82/1.42  tff(f_213, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 2.82/1.42  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.82/1.42  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.82/1.42  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_92, plain, (![B_128, A_129]: (v2_pre_topc(B_128) | ~m1_pre_topc(B_128, A_129) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.82/1.42  tff(c_95, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_92])).
% 2.82/1.42  tff(c_98, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_95])).
% 2.82/1.42  tff(c_75, plain, (![B_117, A_118]: (l1_pre_topc(B_117) | ~m1_pre_topc(B_117, A_118) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.82/1.42  tff(c_78, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_56, c_75])).
% 2.82/1.42  tff(c_81, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_78])).
% 2.82/1.42  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_230, plain, (![C_156, A_157, B_158]: (m1_subset_1(C_156, u1_struct_0(A_157)) | ~m1_subset_1(C_156, u1_struct_0(B_158)) | ~m1_pre_topc(B_158, A_157) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.82/1.42  tff(c_232, plain, (![A_157]: (m1_subset_1('#skF_6', u1_struct_0(A_157)) | ~m1_pre_topc('#skF_5', A_157) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_52, c_230])).
% 2.82/1.42  tff(c_235, plain, (![A_157]: (m1_subset_1('#skF_6', u1_struct_0(A_157)) | ~m1_pre_topc('#skF_5', A_157) | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_58, c_232])).
% 2.82/1.42  tff(c_12, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.82/1.42  tff(c_54, plain, (r1_xboole_0(u1_struct_0('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_99, plain, (![A_130, B_131, C_132]: (~r1_xboole_0(A_130, B_131) | ~r2_hidden(C_132, B_131) | ~r2_hidden(C_132, A_130))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.42  tff(c_106, plain, (![C_133]: (~r2_hidden(C_133, '#skF_4') | ~r2_hidden(C_133, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_54, c_99])).
% 2.82/1.42  tff(c_119, plain, (![A_11]: (~r2_hidden(A_11, '#skF_4') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_11, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_106])).
% 2.82/1.42  tff(c_147, plain, (![A_138]: (~r2_hidden(A_138, '#skF_4') | ~m1_subset_1(A_138, u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_119])).
% 2.82/1.42  tff(c_151, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_147])).
% 2.82/1.42  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_46, plain, (![A_34, B_38, C_40]: (r1_tmap_1(A_34, k6_tmap_1(A_34, B_38), k7_tmap_1(A_34, B_38), C_40) | r2_hidden(C_40, B_38) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_173])).
% 2.82/1.42  tff(c_36, plain, (![A_30, B_31]: (v1_funct_2(k7_tmap_1(A_30, B_31), u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.42  tff(c_178, plain, (![A_144, B_145]: (~v2_struct_0(k6_tmap_1(A_144, B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.82/1.42  tff(c_184, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_178])).
% 2.82/1.42  tff(c_188, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_184])).
% 2.82/1.42  tff(c_189, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_188])).
% 2.82/1.42  tff(c_162, plain, (![A_140, B_141]: (v2_pre_topc(k6_tmap_1(A_140, B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_155])).
% 2.82/1.42  tff(c_168, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_162])).
% 2.82/1.42  tff(c_172, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_168])).
% 2.82/1.42  tff(c_173, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_172])).
% 2.82/1.42  tff(c_191, plain, (![A_147, B_148]: (l1_pre_topc(k6_tmap_1(A_147, B_148)) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_147))) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.82/1.42  tff(c_197, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_191])).
% 2.82/1.42  tff(c_201, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_197])).
% 2.82/1.42  tff(c_202, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_201])).
% 2.82/1.42  tff(c_204, plain, (![A_150, B_151]: (v1_funct_1(k7_tmap_1(A_150, B_151)) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.42  tff(c_210, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_60, c_204])).
% 2.82/1.42  tff(c_214, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_210])).
% 2.82/1.42  tff(c_215, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_214])).
% 2.82/1.42  tff(c_34, plain, (![A_30, B_31]: (m1_subset_1(k7_tmap_1(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.82/1.42  tff(c_264, plain, (![B_172, F_173, A_171, D_175, C_174]: (r1_tmap_1(D_175, A_171, k2_tmap_1(B_172, A_171, C_174, D_175), F_173) | ~r1_tmap_1(B_172, A_171, C_174, F_173) | ~m1_subset_1(F_173, u1_struct_0(D_175)) | ~m1_subset_1(F_173, u1_struct_0(B_172)) | ~m1_pre_topc(D_175, B_172) | v2_struct_0(D_175) | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_172), u1_struct_0(A_171)))) | ~v1_funct_2(C_174, u1_struct_0(B_172), u1_struct_0(A_171)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_172) | ~v2_pre_topc(B_172) | v2_struct_0(B_172) | ~l1_pre_topc(A_171) | ~v2_pre_topc(A_171) | v2_struct_0(A_171))), inference(cnfTransformation, [status(thm)], [f_213])).
% 2.82/1.42  tff(c_268, plain, (![D_176, A_177, B_178, F_179]: (r1_tmap_1(D_176, k6_tmap_1(A_177, B_178), k2_tmap_1(A_177, k6_tmap_1(A_177, B_178), k7_tmap_1(A_177, B_178), D_176), F_179) | ~r1_tmap_1(A_177, k6_tmap_1(A_177, B_178), k7_tmap_1(A_177, B_178), F_179) | ~m1_subset_1(F_179, u1_struct_0(D_176)) | ~m1_subset_1(F_179, u1_struct_0(A_177)) | ~m1_pre_topc(D_176, A_177) | v2_struct_0(D_176) | ~v1_funct_2(k7_tmap_1(A_177, B_178), u1_struct_0(A_177), u1_struct_0(k6_tmap_1(A_177, B_178))) | ~v1_funct_1(k7_tmap_1(A_177, B_178)) | ~l1_pre_topc(k6_tmap_1(A_177, B_178)) | ~v2_pre_topc(k6_tmap_1(A_177, B_178)) | v2_struct_0(k6_tmap_1(A_177, B_178)) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177) | ~v2_pre_topc(A_177) | v2_struct_0(A_177))), inference(resolution, [status(thm)], [c_34, c_264])).
% 2.82/1.42  tff(c_50, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_237])).
% 2.82/1.42  tff(c_271, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_268, c_50])).
% 2.82/1.42  tff(c_274, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_173, c_202, c_215, c_56, c_52, c_271])).
% 2.82/1.42  tff(c_275, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_189, c_58, c_274])).
% 2.82/1.42  tff(c_276, plain, (~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_275])).
% 2.82/1.42  tff(c_279, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_276])).
% 2.82/1.42  tff(c_282, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_279])).
% 2.82/1.42  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_282])).
% 2.82/1.42  tff(c_285, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_275])).
% 2.82/1.42  tff(c_287, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_285])).
% 2.82/1.42  tff(c_290, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_46, c_287])).
% 2.82/1.42  tff(c_293, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_290])).
% 2.82/1.42  tff(c_294, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_151, c_293])).
% 2.82/1.42  tff(c_297, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_235, c_294])).
% 2.82/1.42  tff(c_300, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_297])).
% 2.82/1.42  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_300])).
% 2.82/1.42  tff(c_303, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_285])).
% 2.82/1.42  tff(c_307, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_235, c_303])).
% 2.82/1.42  tff(c_310, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_307])).
% 2.82/1.42  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_310])).
% 2.82/1.42  tff(c_313, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_119])).
% 2.82/1.42  tff(c_325, plain, (![A_181]: (m1_subset_1('#skF_2'(A_181), k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.82/1.42  tff(c_10, plain, (![B_10, A_8]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.82/1.42  tff(c_343, plain, (![A_185]: (v1_xboole_0('#skF_2'(A_185)) | ~v1_xboole_0(u1_struct_0(A_185)) | ~l1_pre_topc(A_185) | ~v2_pre_topc(A_185) | v2_struct_0(A_185))), inference(resolution, [status(thm)], [c_325, c_10])).
% 2.82/1.42  tff(c_346, plain, (v1_xboole_0('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_313, c_343])).
% 2.82/1.42  tff(c_349, plain, (v1_xboole_0('#skF_2'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_81, c_346])).
% 2.82/1.42  tff(c_350, plain, (v1_xboole_0('#skF_2'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_58, c_349])).
% 2.82/1.42  tff(c_24, plain, (![A_26]: (~v1_xboole_0('#skF_2'(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.82/1.42  tff(c_353, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_350, c_24])).
% 2.82/1.42  tff(c_356, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_81, c_353])).
% 2.82/1.42  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_356])).
% 2.82/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  Inference rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Ref     : 0
% 2.82/1.42  #Sup     : 45
% 2.82/1.42  #Fact    : 0
% 2.82/1.42  #Define  : 0
% 2.82/1.42  #Split   : 7
% 2.82/1.42  #Chain   : 0
% 2.82/1.42  #Close   : 0
% 2.82/1.42  
% 2.82/1.42  Ordering : KBO
% 2.82/1.42  
% 2.82/1.42  Simplification rules
% 2.82/1.42  ----------------------
% 2.82/1.42  #Subsume      : 4
% 2.82/1.42  #Demod        : 45
% 2.82/1.42  #Tautology    : 5
% 2.82/1.42  #SimpNegUnit  : 16
% 2.82/1.42  #BackRed      : 0
% 2.82/1.42  
% 2.82/1.42  #Partial instantiations: 0
% 2.82/1.42  #Strategies tried      : 1
% 2.82/1.42  
% 2.82/1.42  Timing (in seconds)
% 2.82/1.42  ----------------------
% 2.82/1.42  Preprocessing        : 0.35
% 2.82/1.42  Parsing              : 0.19
% 2.82/1.42  CNF conversion       : 0.03
% 2.82/1.42  Main loop            : 0.28
% 2.82/1.42  Inferencing          : 0.11
% 2.82/1.42  Reduction            : 0.08
% 2.82/1.42  Demodulation         : 0.05
% 2.82/1.42  BG Simplification    : 0.02
% 2.82/1.42  Subsumption          : 0.06
% 2.82/1.42  Abstraction          : 0.01
% 2.82/1.42  MUC search           : 0.00
% 2.82/1.42  Cooper               : 0.00
% 2.82/1.42  Total                : 0.68
% 2.82/1.42  Index Insertion      : 0.00
% 2.82/1.42  Index Deletion       : 0.00
% 2.82/1.42  Index Matching       : 0.00
% 2.82/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

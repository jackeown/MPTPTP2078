%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:55 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 362 expanded)
%              Number of leaves         :   39 ( 153 expanded)
%              Depth                    :   14
%              Number of atoms          :  289 (1616 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_219,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => m1_subset_1(C,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_155,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tmap_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_195,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(f_75,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_52,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_64,plain,(
    ! [B_108,A_109] :
      ( l1_pre_topc(B_108)
      | ~ m1_pre_topc(B_108,A_109)
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_67,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_64])).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_67])).

tff(c_16,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_342,plain,(
    ! [C_156,A_157,B_158] :
      ( m1_subset_1(C_156,u1_struct_0(A_157))
      | ~ m1_subset_1(C_156,u1_struct_0(B_158))
      | ~ m1_pre_topc(B_158,A_157)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_353,plain,(
    ! [A_157] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_157))
      | ~ m1_pre_topc('#skF_4',A_157)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_48,c_342])).

tff(c_359,plain,(
    ! [A_157] :
      ( m1_subset_1('#skF_5',u1_struct_0(A_157))
      | ~ m1_pre_topc('#skF_4',A_157)
      | ~ l1_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_353])).

tff(c_73,plain,(
    ! [B_113,A_114] :
      ( v1_xboole_0(B_113)
      | ~ m1_subset_1(B_113,A_114)
      | ~ v1_xboole_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_85,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_73])).

tff(c_87,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r2_hidden(B_7,A_6)
      | ~ m1_subset_1(B_7,A_6)
      | v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_104,plain,(
    ! [A_123,B_124,C_125] :
      ( ~ r1_xboole_0(A_123,B_124)
      | ~ r2_hidden(C_125,B_124)
      | ~ r2_hidden(C_125,A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    ! [C_126] :
      ( ~ r2_hidden(C_126,'#skF_3')
      | ~ r2_hidden(C_126,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_116,plain,(
    ! [B_7] :
      ( ~ r2_hidden(B_7,'#skF_3')
      | ~ m1_subset_1(B_7,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_108])).

tff(c_139,plain,(
    ! [B_129] :
      ( ~ r2_hidden(B_129,'#skF_3')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_116])).

tff(c_148,plain,(
    ~ r2_hidden('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_139])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_42,plain,(
    ! [A_26,B_30,C_32] :
      ( r1_tmap_1(A_26,k6_tmap_1(A_26,B_30),k7_tmap_1(A_26,B_30),C_32)
      | r2_hidden(C_32,B_30)
      | ~ m1_subset_1(C_32,u1_struct_0(A_26))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( v1_funct_2(k7_tmap_1(A_22,B_23),u1_struct_0(A_22),u1_struct_0(k6_tmap_1(A_22,B_23)))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_268,plain,(
    ! [A_140,B_141] :
      ( ~ v2_struct_0(k6_tmap_1(A_140,B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_283,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_268])).

tff(c_289,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_283])).

tff(c_290,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_289])).

tff(c_314,plain,(
    ! [A_144,B_145] :
      ( v2_pre_topc(k6_tmap_1(A_144,B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_329,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_314])).

tff(c_335,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_329])).

tff(c_336,plain,(
    v2_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_335])).

tff(c_126,plain,(
    ! [A_127,B_128] :
      ( l1_pre_topc(k6_tmap_1(A_127,B_128))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_133,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_126])).

tff(c_137,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_133])).

tff(c_138,plain,(
    l1_pre_topc(k6_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_137])).

tff(c_193,plain,(
    ! [A_134,B_135] :
      ( v1_funct_1(k7_tmap_1(A_134,B_135))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134)
      | ~ v2_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_208,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_193])).

tff(c_214,plain,
    ( v1_funct_1(k7_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_208])).

tff(c_215,plain,(
    v1_funct_1(k7_tmap_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_214])).

tff(c_30,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k7_tmap_1(A_22,B_23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22),u1_struct_0(k6_tmap_1(A_22,B_23)))))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(u1_struct_0(A_22)))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_501,plain,(
    ! [F_192,A_190,B_191,D_193,C_194] :
      ( r1_tmap_1(D_193,A_190,k2_tmap_1(B_191,A_190,C_194,D_193),F_192)
      | ~ r1_tmap_1(B_191,A_190,C_194,F_192)
      | ~ m1_subset_1(F_192,u1_struct_0(D_193))
      | ~ m1_subset_1(F_192,u1_struct_0(B_191))
      | ~ m1_pre_topc(D_193,B_191)
      | v2_struct_0(D_193)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_191),u1_struct_0(A_190))))
      | ~ v1_funct_2(C_194,u1_struct_0(B_191),u1_struct_0(A_190))
      | ~ v1_funct_1(C_194)
      | ~ l1_pre_topc(B_191)
      | ~ v2_pre_topc(B_191)
      | v2_struct_0(B_191)
      | ~ l1_pre_topc(A_190)
      | ~ v2_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_662,plain,(
    ! [D_257,A_258,B_259,F_260] :
      ( r1_tmap_1(D_257,k6_tmap_1(A_258,B_259),k2_tmap_1(A_258,k6_tmap_1(A_258,B_259),k7_tmap_1(A_258,B_259),D_257),F_260)
      | ~ r1_tmap_1(A_258,k6_tmap_1(A_258,B_259),k7_tmap_1(A_258,B_259),F_260)
      | ~ m1_subset_1(F_260,u1_struct_0(D_257))
      | ~ m1_subset_1(F_260,u1_struct_0(A_258))
      | ~ m1_pre_topc(D_257,A_258)
      | v2_struct_0(D_257)
      | ~ v1_funct_2(k7_tmap_1(A_258,B_259),u1_struct_0(A_258),u1_struct_0(k6_tmap_1(A_258,B_259)))
      | ~ v1_funct_1(k7_tmap_1(A_258,B_259))
      | ~ l1_pre_topc(k6_tmap_1(A_258,B_259))
      | ~ v2_pre_topc(k6_tmap_1(A_258,B_259))
      | v2_struct_0(k6_tmap_1(A_258,B_259))
      | ~ m1_subset_1(B_259,k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_30,c_501])).

tff(c_46,plain,(
    ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_2','#skF_3'),k2_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_665,plain,
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
    inference(resolution,[status(thm)],[c_662,c_46])).

tff(c_668,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4')
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3')))
    | v2_struct_0(k6_tmap_1('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_336,c_138,c_215,c_52,c_48,c_665])).

tff(c_669,plain,
    ( ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_290,c_54,c_668])).

tff(c_670,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_2','#skF_3'),u1_struct_0('#skF_2'),u1_struct_0(k6_tmap_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_673,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_670])).

tff(c_676,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_673])).

tff(c_678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_676])).

tff(c_679,plain,
    ( ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_688,plain,(
    ~ r1_tmap_1('#skF_2',k6_tmap_1('#skF_2','#skF_3'),k7_tmap_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_679])).

tff(c_691,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_688])).

tff(c_694,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_691])).

tff(c_695,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_148,c_694])).

tff(c_698,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_359,c_695])).

tff(c_704,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_698])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_704])).

tff(c_707,plain,(
    ~ m1_subset_1('#skF_5',u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_679])).

tff(c_711,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_359,c_707])).

tff(c_717,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52,c_711])).

tff(c_719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_717])).

tff(c_721,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_20,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_725,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_721,c_20])).

tff(c_728,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_725])).

tff(c_731,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_728])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:14:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.55  
% 3.58/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.56  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.58/1.56  
% 3.58/1.56  %Foreground sorts:
% 3.58/1.56  
% 3.58/1.56  
% 3.58/1.56  %Background operators:
% 3.58/1.56  
% 3.58/1.56  
% 3.58/1.56  %Foreground operators:
% 3.58/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.58/1.56  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 3.58/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.56  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.58/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.58/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.58/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.58/1.56  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.58/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.58/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.56  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.58/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.58/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.58/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.56  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 3.58/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.58/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.58/1.56  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.58/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.58/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.58/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.58/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.58/1.56  
% 3.58/1.58  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tmap_1)).
% 3.58/1.58  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.58/1.58  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.58/1.58  tff(f_91, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 3.58/1.58  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.58/1.58  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.58/1.58  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_tmap_1)).
% 3.58/1.58  tff(f_121, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 3.58/1.58  tff(f_137, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 3.58/1.58  tff(f_106, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.58/1.58  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.58/1.58  tff(f_75, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.58/1.58  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_52, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_64, plain, (![B_108, A_109]: (l1_pre_topc(B_108) | ~m1_pre_topc(B_108, A_109) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.58/1.58  tff(c_67, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_52, c_64])).
% 3.58/1.58  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_67])).
% 3.58/1.58  tff(c_16, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.58/1.58  tff(c_54, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_48, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_342, plain, (![C_156, A_157, B_158]: (m1_subset_1(C_156, u1_struct_0(A_157)) | ~m1_subset_1(C_156, u1_struct_0(B_158)) | ~m1_pre_topc(B_158, A_157) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.58/1.58  tff(c_353, plain, (![A_157]: (m1_subset_1('#skF_5', u1_struct_0(A_157)) | ~m1_pre_topc('#skF_4', A_157) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_48, c_342])).
% 3.58/1.58  tff(c_359, plain, (![A_157]: (m1_subset_1('#skF_5', u1_struct_0(A_157)) | ~m1_pre_topc('#skF_4', A_157) | ~l1_pre_topc(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_54, c_353])).
% 3.58/1.58  tff(c_73, plain, (![B_113, A_114]: (v1_xboole_0(B_113) | ~m1_subset_1(B_113, A_114) | ~v1_xboole_0(A_114))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.58/1.58  tff(c_85, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_73])).
% 3.58/1.58  tff(c_87, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_85])).
% 3.58/1.58  tff(c_10, plain, (![B_7, A_6]: (r2_hidden(B_7, A_6) | ~m1_subset_1(B_7, A_6) | v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.58/1.58  tff(c_50, plain, (r1_xboole_0(u1_struct_0('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_104, plain, (![A_123, B_124, C_125]: (~r1_xboole_0(A_123, B_124) | ~r2_hidden(C_125, B_124) | ~r2_hidden(C_125, A_123))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.58/1.58  tff(c_108, plain, (![C_126]: (~r2_hidden(C_126, '#skF_3') | ~r2_hidden(C_126, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_50, c_104])).
% 3.58/1.58  tff(c_116, plain, (![B_7]: (~r2_hidden(B_7, '#skF_3') | ~m1_subset_1(B_7, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_108])).
% 3.58/1.58  tff(c_139, plain, (![B_129]: (~r2_hidden(B_129, '#skF_3') | ~m1_subset_1(B_129, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_87, c_116])).
% 3.58/1.58  tff(c_148, plain, (~r2_hidden('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_139])).
% 3.58/1.58  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_42, plain, (![A_26, B_30, C_32]: (r1_tmap_1(A_26, k6_tmap_1(A_26, B_30), k7_tmap_1(A_26, B_30), C_32) | r2_hidden(C_32, B_30) | ~m1_subset_1(C_32, u1_struct_0(A_26)) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.58/1.58  tff(c_32, plain, (![A_22, B_23]: (v1_funct_2(k7_tmap_1(A_22, B_23), u1_struct_0(A_22), u1_struct_0(k6_tmap_1(A_22, B_23))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.58/1.58  tff(c_268, plain, (![A_140, B_141]: (~v2_struct_0(k6_tmap_1(A_140, B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.58/1.58  tff(c_283, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_268])).
% 3.58/1.58  tff(c_289, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_283])).
% 3.58/1.58  tff(c_290, plain, (~v2_struct_0(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_289])).
% 3.58/1.58  tff(c_314, plain, (![A_144, B_145]: (v2_pre_topc(k6_tmap_1(A_144, B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.58/1.58  tff(c_329, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_314])).
% 3.58/1.58  tff(c_335, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_329])).
% 3.58/1.58  tff(c_336, plain, (v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_335])).
% 3.58/1.58  tff(c_126, plain, (![A_127, B_128]: (l1_pre_topc(k6_tmap_1(A_127, B_128)) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.58/1.58  tff(c_133, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_126])).
% 3.58/1.58  tff(c_137, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_133])).
% 3.58/1.58  tff(c_138, plain, (l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_137])).
% 3.58/1.58  tff(c_193, plain, (![A_134, B_135]: (v1_funct_1(k7_tmap_1(A_134, B_135)) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134) | ~v2_pre_topc(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.58/1.58  tff(c_208, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_56, c_193])).
% 3.58/1.58  tff(c_214, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_208])).
% 3.58/1.58  tff(c_215, plain, (v1_funct_1(k7_tmap_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_62, c_214])).
% 3.58/1.58  tff(c_30, plain, (![A_22, B_23]: (m1_subset_1(k7_tmap_1(A_22, B_23), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22), u1_struct_0(k6_tmap_1(A_22, B_23))))) | ~m1_subset_1(B_23, k1_zfmisc_1(u1_struct_0(A_22))) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.58/1.58  tff(c_501, plain, (![F_192, A_190, B_191, D_193, C_194]: (r1_tmap_1(D_193, A_190, k2_tmap_1(B_191, A_190, C_194, D_193), F_192) | ~r1_tmap_1(B_191, A_190, C_194, F_192) | ~m1_subset_1(F_192, u1_struct_0(D_193)) | ~m1_subset_1(F_192, u1_struct_0(B_191)) | ~m1_pre_topc(D_193, B_191) | v2_struct_0(D_193) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_191), u1_struct_0(A_190)))) | ~v1_funct_2(C_194, u1_struct_0(B_191), u1_struct_0(A_190)) | ~v1_funct_1(C_194) | ~l1_pre_topc(B_191) | ~v2_pre_topc(B_191) | v2_struct_0(B_191) | ~l1_pre_topc(A_190) | ~v2_pre_topc(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_195])).
% 3.58/1.58  tff(c_662, plain, (![D_257, A_258, B_259, F_260]: (r1_tmap_1(D_257, k6_tmap_1(A_258, B_259), k2_tmap_1(A_258, k6_tmap_1(A_258, B_259), k7_tmap_1(A_258, B_259), D_257), F_260) | ~r1_tmap_1(A_258, k6_tmap_1(A_258, B_259), k7_tmap_1(A_258, B_259), F_260) | ~m1_subset_1(F_260, u1_struct_0(D_257)) | ~m1_subset_1(F_260, u1_struct_0(A_258)) | ~m1_pre_topc(D_257, A_258) | v2_struct_0(D_257) | ~v1_funct_2(k7_tmap_1(A_258, B_259), u1_struct_0(A_258), u1_struct_0(k6_tmap_1(A_258, B_259))) | ~v1_funct_1(k7_tmap_1(A_258, B_259)) | ~l1_pre_topc(k6_tmap_1(A_258, B_259)) | ~v2_pre_topc(k6_tmap_1(A_258, B_259)) | v2_struct_0(k6_tmap_1(A_258, B_259)) | ~m1_subset_1(B_259, k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(resolution, [status(thm)], [c_30, c_501])).
% 3.58/1.58  tff(c_46, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_2', '#skF_3'), k2_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.58/1.58  tff(c_665, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | ~v1_funct_1(k7_tmap_1('#skF_2', '#skF_3')) | ~l1_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | ~v2_pre_topc(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_662, c_46])).
% 3.58/1.58  tff(c_668, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_4') | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3'))) | v2_struct_0(k6_tmap_1('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_336, c_138, c_215, c_52, c_48, c_665])).
% 3.58/1.58  tff(c_669, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_62, c_290, c_54, c_668])).
% 3.58/1.58  tff(c_670, plain, (~v1_funct_2(k7_tmap_1('#skF_2', '#skF_3'), u1_struct_0('#skF_2'), u1_struct_0(k6_tmap_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_669])).
% 3.58/1.58  tff(c_673, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_670])).
% 3.58/1.58  tff(c_676, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_673])).
% 3.58/1.58  tff(c_678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_676])).
% 3.58/1.58  tff(c_679, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_669])).
% 3.58/1.58  tff(c_688, plain, (~r1_tmap_1('#skF_2', k6_tmap_1('#skF_2', '#skF_3'), k7_tmap_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_679])).
% 3.58/1.58  tff(c_691, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_688])).
% 3.58/1.58  tff(c_694, plain, (r2_hidden('#skF_5', '#skF_3') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_691])).
% 3.58/1.58  tff(c_695, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_62, c_148, c_694])).
% 3.58/1.58  tff(c_698, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_359, c_695])).
% 3.58/1.58  tff(c_704, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_698])).
% 3.58/1.58  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_704])).
% 3.58/1.58  tff(c_707, plain, (~m1_subset_1('#skF_5', u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_679])).
% 3.58/1.58  tff(c_711, plain, (~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_359, c_707])).
% 3.58/1.58  tff(c_717, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52, c_711])).
% 3.58/1.58  tff(c_719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_717])).
% 3.58/1.58  tff(c_721, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_85])).
% 3.58/1.58  tff(c_20, plain, (![A_12]: (~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.58/1.58  tff(c_725, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_721, c_20])).
% 3.58/1.58  tff(c_728, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_54, c_725])).
% 3.58/1.58  tff(c_731, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_728])).
% 3.58/1.58  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_731])).
% 3.58/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.58/1.58  
% 3.58/1.58  Inference rules
% 3.58/1.58  ----------------------
% 3.58/1.58  #Ref     : 0
% 3.58/1.58  #Sup     : 115
% 3.58/1.58  #Fact    : 0
% 3.58/1.58  #Define  : 0
% 3.58/1.58  #Split   : 11
% 3.58/1.58  #Chain   : 0
% 3.58/1.58  #Close   : 0
% 3.58/1.58  
% 3.58/1.58  Ordering : KBO
% 3.58/1.58  
% 3.58/1.58  Simplification rules
% 3.58/1.58  ----------------------
% 3.58/1.58  #Subsume      : 26
% 3.58/1.58  #Demod        : 53
% 3.58/1.58  #Tautology    : 10
% 3.58/1.58  #SimpNegUnit  : 40
% 3.58/1.58  #BackRed      : 0
% 3.58/1.58  
% 3.58/1.58  #Partial instantiations: 0
% 3.58/1.58  #Strategies tried      : 1
% 3.58/1.58  
% 3.58/1.58  Timing (in seconds)
% 3.58/1.58  ----------------------
% 3.58/1.58  Preprocessing        : 0.36
% 3.58/1.58  Parsing              : 0.20
% 3.58/1.58  CNF conversion       : 0.03
% 3.58/1.58  Main loop            : 0.44
% 3.58/1.58  Inferencing          : 0.17
% 3.58/1.58  Reduction            : 0.12
% 3.58/1.58  Demodulation         : 0.08
% 3.58/1.58  BG Simplification    : 0.02
% 3.58/1.58  Subsumption          : 0.10
% 3.58/1.58  Abstraction          : 0.02
% 3.58/1.58  MUC search           : 0.00
% 3.58/1.58  Cooper               : 0.00
% 3.58/1.58  Total                : 0.84
% 3.58/1.58  Index Insertion      : 0.00
% 3.58/1.58  Index Deletion       : 0.00
% 3.58/1.58  Index Matching       : 0.00
% 3.58/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

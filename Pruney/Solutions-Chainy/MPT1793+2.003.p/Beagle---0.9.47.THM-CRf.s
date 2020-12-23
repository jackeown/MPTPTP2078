%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:53 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 395 expanded)
%              Number of leaves         :   41 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  314 (1751 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v2_compts_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k7_tmap_1,type,(
    k7_tmap_1: ( $i * $i ) > $i )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_235,negated_conjecture,(
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

tff(f_171,axiom,(
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

tff(f_137,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_153,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_211,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v2_compts_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_compts_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_62,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_112,plain,(
    ! [B_131,A_132] :
      ( v2_pre_topc(B_131)
      | ~ m1_pre_topc(B_131,A_132)
      | ~ l1_pre_topc(A_132)
      | ~ v2_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_115,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_112])).

tff(c_118,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_115])).

tff(c_73,plain,(
    ! [B_117,A_118] :
      ( l1_pre_topc(B_117)
      | ~ m1_pre_topc(B_117,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_76,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_79,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_76])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_228,plain,(
    ! [C_155,A_156,B_157] :
      ( m1_subset_1(C_155,u1_struct_0(A_156))
      | ~ m1_subset_1(C_155,u1_struct_0(B_157))
      | ~ m1_pre_topc(B_157,A_156)
      | v2_struct_0(B_157)
      | ~ l1_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_230,plain,(
    ! [A_156] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_156))
      | ~ m1_pre_topc('#skF_5',A_156)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(resolution,[status(thm)],[c_50,c_228])).

tff(c_233,plain,(
    ! [A_156] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_156))
      | ~ m1_pre_topc('#skF_5',A_156)
      | ~ l1_pre_topc(A_156)
      | v2_struct_0(A_156) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_230])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_52,plain,(
    r1_xboole_0(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_89,plain,(
    ! [A_127,B_128,C_129] :
      ( ~ r1_xboole_0(A_127,B_128)
      | ~ r2_hidden(C_129,B_128)
      | ~ r2_hidden(C_129,A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_96,plain,(
    ! [C_130] :
      ( ~ r2_hidden(C_130,'#skF_4')
      | ~ r2_hidden(C_130,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_110,plain,(
    ! [A_11] :
      ( ~ r2_hidden(A_11,'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_11,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_133,plain,(
    ! [A_136] :
      ( ~ r2_hidden(A_136,'#skF_4')
      | ~ m1_subset_1(A_136,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_137,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_133])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_44,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_tmap_1(A_34,k6_tmap_1(A_34,B_38),k7_tmap_1(A_34,B_38),C_40)
      | r2_hidden(C_40,B_38)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( v1_funct_2(k7_tmap_1(A_30,B_31),u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_202,plain,(
    ! [A_149,B_150] :
      ( ~ v2_struct_0(k6_tmap_1(A_149,B_150))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_208,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_202])).

tff(c_212,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_208])).

tff(c_213,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_212])).

tff(c_160,plain,(
    ! [A_140,B_141] :
      ( v2_pre_topc(k6_tmap_1(A_140,B_141))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_166,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_160])).

tff(c_170,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_166])).

tff(c_171,plain,(
    v2_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_170])).

tff(c_189,plain,(
    ! [A_146,B_147] :
      ( l1_pre_topc(k6_tmap_1(A_146,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_195,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_189])).

tff(c_199,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_195])).

tff(c_200,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_199])).

tff(c_176,plain,(
    ! [A_143,B_144] :
      ( v1_funct_1(k7_tmap_1(A_143,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_182,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_176])).

tff(c_186,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_182])).

tff(c_187,plain,(
    v1_funct_1(k7_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_186])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k7_tmap_1(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_262,plain,(
    ! [A_170,C_173,B_171,F_172,D_174] :
      ( r1_tmap_1(D_174,A_170,k2_tmap_1(B_171,A_170,C_173,D_174),F_172)
      | ~ r1_tmap_1(B_171,A_170,C_173,F_172)
      | ~ m1_subset_1(F_172,u1_struct_0(D_174))
      | ~ m1_subset_1(F_172,u1_struct_0(B_171))
      | ~ m1_pre_topc(D_174,B_171)
      | v2_struct_0(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_171),u1_struct_0(A_170))))
      | ~ v1_funct_2(C_173,u1_struct_0(B_171),u1_struct_0(A_170))
      | ~ v1_funct_1(C_173)
      | ~ l1_pre_topc(B_171)
      | ~ v2_pre_topc(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_170)
      | ~ v2_pre_topc(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_266,plain,(
    ! [D_175,A_176,B_177,F_178] :
      ( r1_tmap_1(D_175,k6_tmap_1(A_176,B_177),k2_tmap_1(A_176,k6_tmap_1(A_176,B_177),k7_tmap_1(A_176,B_177),D_175),F_178)
      | ~ r1_tmap_1(A_176,k6_tmap_1(A_176,B_177),k7_tmap_1(A_176,B_177),F_178)
      | ~ m1_subset_1(F_178,u1_struct_0(D_175))
      | ~ m1_subset_1(F_178,u1_struct_0(A_176))
      | ~ m1_pre_topc(D_175,A_176)
      | v2_struct_0(D_175)
      | ~ v1_funct_2(k7_tmap_1(A_176,B_177),u1_struct_0(A_176),u1_struct_0(k6_tmap_1(A_176,B_177)))
      | ~ v1_funct_1(k7_tmap_1(A_176,B_177))
      | ~ l1_pre_topc(k6_tmap_1(A_176,B_177))
      | ~ v2_pre_topc(k6_tmap_1(A_176,B_177))
      | v2_struct_0(k6_tmap_1(A_176,B_177))
      | ~ m1_subset_1(B_177,k1_zfmisc_1(u1_struct_0(A_176)))
      | ~ l1_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_32,c_262])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_269,plain,
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
    inference(resolution,[status(thm)],[c_266,c_48])).

tff(c_272,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_5')
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_171,c_200,c_187,c_54,c_50,c_269])).

tff(c_273,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_213,c_56,c_272])).

tff(c_274,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_277,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_274])).

tff(c_280,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_277])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_280])).

tff(c_283,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_285,plain,(
    ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_288,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_285])).

tff(c_291,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_288])).

tff(c_292,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_137,c_291])).

tff(c_295,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_233,c_292])).

tff(c_298,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_295])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_298])).

tff(c_301,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_305,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_233,c_301])).

tff(c_308,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_305])).

tff(c_310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_308])).

tff(c_311,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_323,plain,(
    ! [A_180] :
      ( m1_subset_1('#skF_2'(A_180),k1_zfmisc_1(u1_struct_0(A_180)))
      | ~ l1_pre_topc(A_180)
      | ~ v2_pre_topc(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_341,plain,(
    ! [A_184] :
      ( v1_xboole_0('#skF_2'(A_184))
      | ~ v1_xboole_0(u1_struct_0(A_184))
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184) ) ),
    inference(resolution,[status(thm)],[c_323,c_10])).

tff(c_344,plain,
    ( v1_xboole_0('#skF_2'('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_311,c_341])).

tff(c_347,plain,
    ( v1_xboole_0('#skF_2'('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_79,c_344])).

tff(c_348,plain,(
    v1_xboole_0('#skF_2'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_347])).

tff(c_22,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0('#skF_2'(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_351,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_348,c_22])).

tff(c_354,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_79,c_351])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_354])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:09:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  %$ r1_tmap_1 > v1_funct_2 > v2_compts_1 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.81/1.41  
% 2.81/1.41  %Foreground sorts:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Background operators:
% 2.81/1.41  
% 2.81/1.41  
% 2.81/1.41  %Foreground operators:
% 2.81/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.81/1.41  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 2.81/1.41  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 2.81/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.41  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.81/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.81/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.81/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.41  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.81/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.41  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.81/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.81/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.81/1.41  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.81/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.81/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.41  
% 2.81/1.43  tff(f_235, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 2.81/1.43  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.81/1.43  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.81/1.43  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 2.81/1.43  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.81/1.43  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.81/1.43  tff(f_171, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 2.81/1.43  tff(f_137, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 2.81/1.43  tff(f_153, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 2.81/1.43  tff(f_122, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.81/1.43  tff(f_211, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 2.81/1.43  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: ((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v2_compts_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_compts_1)).
% 2.81/1.43  tff(f_54, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.81/1.43  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_62, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_112, plain, (![B_131, A_132]: (v2_pre_topc(B_131) | ~m1_pre_topc(B_131, A_132) | ~l1_pre_topc(A_132) | ~v2_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.81/1.43  tff(c_115, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_112])).
% 2.81/1.43  tff(c_118, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_115])).
% 2.81/1.43  tff(c_73, plain, (![B_117, A_118]: (l1_pre_topc(B_117) | ~m1_pre_topc(B_117, A_118) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.81/1.43  tff(c_76, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_73])).
% 2.81/1.43  tff(c_79, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_76])).
% 2.81/1.43  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_228, plain, (![C_155, A_156, B_157]: (m1_subset_1(C_155, u1_struct_0(A_156)) | ~m1_subset_1(C_155, u1_struct_0(B_157)) | ~m1_pre_topc(B_157, A_156) | v2_struct_0(B_157) | ~l1_pre_topc(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.81/1.43  tff(c_230, plain, (![A_156]: (m1_subset_1('#skF_6', u1_struct_0(A_156)) | ~m1_pre_topc('#skF_5', A_156) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_156) | v2_struct_0(A_156))), inference(resolution, [status(thm)], [c_50, c_228])).
% 2.81/1.43  tff(c_233, plain, (![A_156]: (m1_subset_1('#skF_6', u1_struct_0(A_156)) | ~m1_pre_topc('#skF_5', A_156) | ~l1_pre_topc(A_156) | v2_struct_0(A_156))), inference(negUnitSimplification, [status(thm)], [c_56, c_230])).
% 2.81/1.43  tff(c_12, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.81/1.43  tff(c_52, plain, (r1_xboole_0(u1_struct_0('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_89, plain, (![A_127, B_128, C_129]: (~r1_xboole_0(A_127, B_128) | ~r2_hidden(C_129, B_128) | ~r2_hidden(C_129, A_127))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.43  tff(c_96, plain, (![C_130]: (~r2_hidden(C_130, '#skF_4') | ~r2_hidden(C_130, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_52, c_89])).
% 2.81/1.43  tff(c_110, plain, (![A_11]: (~r2_hidden(A_11, '#skF_4') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_11, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.81/1.43  tff(c_133, plain, (![A_136]: (~r2_hidden(A_136, '#skF_4') | ~m1_subset_1(A_136, u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_110])).
% 2.81/1.43  tff(c_137, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_133])).
% 2.81/1.43  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_44, plain, (![A_34, B_38, C_40]: (r1_tmap_1(A_34, k6_tmap_1(A_34, B_38), k7_tmap_1(A_34, B_38), C_40) | r2_hidden(C_40, B_38) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_171])).
% 2.81/1.43  tff(c_34, plain, (![A_30, B_31]: (v1_funct_2(k7_tmap_1(A_30, B_31), u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.81/1.43  tff(c_202, plain, (![A_149, B_150]: (~v2_struct_0(k6_tmap_1(A_149, B_150)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.43  tff(c_208, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_202])).
% 2.81/1.43  tff(c_212, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_208])).
% 2.81/1.43  tff(c_213, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_212])).
% 2.81/1.43  tff(c_160, plain, (![A_140, B_141]: (v2_pre_topc(k6_tmap_1(A_140, B_141)) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_153])).
% 2.81/1.43  tff(c_166, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_160])).
% 2.81/1.43  tff(c_170, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_166])).
% 2.81/1.43  tff(c_171, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_170])).
% 2.81/1.43  tff(c_189, plain, (![A_146, B_147]: (l1_pre_topc(k6_tmap_1(A_146, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.81/1.43  tff(c_195, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_189])).
% 2.81/1.43  tff(c_199, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_195])).
% 2.81/1.43  tff(c_200, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_199])).
% 2.81/1.43  tff(c_176, plain, (![A_143, B_144]: (v1_funct_1(k7_tmap_1(A_143, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.81/1.43  tff(c_182, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_176])).
% 2.81/1.43  tff(c_186, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_182])).
% 2.81/1.43  tff(c_187, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_186])).
% 2.81/1.43  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(k7_tmap_1(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.81/1.43  tff(c_262, plain, (![A_170, C_173, B_171, F_172, D_174]: (r1_tmap_1(D_174, A_170, k2_tmap_1(B_171, A_170, C_173, D_174), F_172) | ~r1_tmap_1(B_171, A_170, C_173, F_172) | ~m1_subset_1(F_172, u1_struct_0(D_174)) | ~m1_subset_1(F_172, u1_struct_0(B_171)) | ~m1_pre_topc(D_174, B_171) | v2_struct_0(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_171), u1_struct_0(A_170)))) | ~v1_funct_2(C_173, u1_struct_0(B_171), u1_struct_0(A_170)) | ~v1_funct_1(C_173) | ~l1_pre_topc(B_171) | ~v2_pre_topc(B_171) | v2_struct_0(B_171) | ~l1_pre_topc(A_170) | ~v2_pre_topc(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_211])).
% 2.81/1.43  tff(c_266, plain, (![D_175, A_176, B_177, F_178]: (r1_tmap_1(D_175, k6_tmap_1(A_176, B_177), k2_tmap_1(A_176, k6_tmap_1(A_176, B_177), k7_tmap_1(A_176, B_177), D_175), F_178) | ~r1_tmap_1(A_176, k6_tmap_1(A_176, B_177), k7_tmap_1(A_176, B_177), F_178) | ~m1_subset_1(F_178, u1_struct_0(D_175)) | ~m1_subset_1(F_178, u1_struct_0(A_176)) | ~m1_pre_topc(D_175, A_176) | v2_struct_0(D_175) | ~v1_funct_2(k7_tmap_1(A_176, B_177), u1_struct_0(A_176), u1_struct_0(k6_tmap_1(A_176, B_177))) | ~v1_funct_1(k7_tmap_1(A_176, B_177)) | ~l1_pre_topc(k6_tmap_1(A_176, B_177)) | ~v2_pre_topc(k6_tmap_1(A_176, B_177)) | v2_struct_0(k6_tmap_1(A_176, B_177)) | ~m1_subset_1(B_177, k1_zfmisc_1(u1_struct_0(A_176))) | ~l1_pre_topc(A_176) | ~v2_pre_topc(A_176) | v2_struct_0(A_176))), inference(resolution, [status(thm)], [c_32, c_262])).
% 2.81/1.43  tff(c_48, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_235])).
% 2.81/1.43  tff(c_269, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_266, c_48])).
% 2.81/1.43  tff(c_272, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_171, c_200, c_187, c_54, c_50, c_269])).
% 2.81/1.43  tff(c_273, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_64, c_213, c_56, c_272])).
% 2.81/1.43  tff(c_274, plain, (~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_273])).
% 2.81/1.43  tff(c_277, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_274])).
% 2.81/1.43  tff(c_280, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_277])).
% 2.81/1.43  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_280])).
% 2.81/1.43  tff(c_283, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_273])).
% 2.81/1.43  tff(c_285, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_283])).
% 2.81/1.43  tff(c_288, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_285])).
% 2.81/1.43  tff(c_291, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_288])).
% 2.81/1.43  tff(c_292, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_137, c_291])).
% 2.81/1.43  tff(c_295, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_233, c_292])).
% 2.81/1.43  tff(c_298, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_295])).
% 2.81/1.43  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_298])).
% 2.81/1.43  tff(c_301, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_283])).
% 2.81/1.43  tff(c_305, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_233, c_301])).
% 2.81/1.43  tff(c_308, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_305])).
% 2.81/1.43  tff(c_310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_308])).
% 2.81/1.43  tff(c_311, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_110])).
% 2.81/1.43  tff(c_323, plain, (![A_180]: (m1_subset_1('#skF_2'(A_180), k1_zfmisc_1(u1_struct_0(A_180))) | ~l1_pre_topc(A_180) | ~v2_pre_topc(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.81/1.43  tff(c_10, plain, (![B_10, A_8]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.43  tff(c_341, plain, (![A_184]: (v1_xboole_0('#skF_2'(A_184)) | ~v1_xboole_0(u1_struct_0(A_184)) | ~l1_pre_topc(A_184) | ~v2_pre_topc(A_184) | v2_struct_0(A_184))), inference(resolution, [status(thm)], [c_323, c_10])).
% 2.81/1.43  tff(c_344, plain, (v1_xboole_0('#skF_2'('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_311, c_341])).
% 2.81/1.43  tff(c_347, plain, (v1_xboole_0('#skF_2'('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_79, c_344])).
% 2.81/1.43  tff(c_348, plain, (v1_xboole_0('#skF_2'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_56, c_347])).
% 2.81/1.43  tff(c_22, plain, (![A_26]: (~v1_xboole_0('#skF_2'(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.81/1.43  tff(c_351, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_348, c_22])).
% 2.81/1.43  tff(c_354, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_79, c_351])).
% 2.81/1.43  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_354])).
% 2.81/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.43  
% 2.81/1.43  Inference rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Ref     : 0
% 2.81/1.43  #Sup     : 45
% 2.81/1.43  #Fact    : 0
% 2.81/1.43  #Define  : 0
% 2.81/1.43  #Split   : 8
% 2.81/1.43  #Chain   : 0
% 2.81/1.43  #Close   : 0
% 2.81/1.43  
% 2.81/1.43  Ordering : KBO
% 2.81/1.43  
% 2.81/1.43  Simplification rules
% 2.81/1.43  ----------------------
% 2.81/1.43  #Subsume      : 4
% 2.81/1.43  #Demod        : 45
% 2.81/1.43  #Tautology    : 5
% 2.81/1.43  #SimpNegUnit  : 16
% 2.81/1.43  #BackRed      : 0
% 2.81/1.43  
% 2.81/1.43  #Partial instantiations: 0
% 2.81/1.43  #Strategies tried      : 1
% 2.81/1.43  
% 2.81/1.43  Timing (in seconds)
% 2.81/1.43  ----------------------
% 2.81/1.44  Preprocessing        : 0.34
% 2.81/1.44  Parsing              : 0.19
% 2.81/1.44  CNF conversion       : 0.03
% 2.81/1.44  Main loop            : 0.28
% 2.81/1.44  Inferencing          : 0.11
% 2.81/1.44  Reduction            : 0.08
% 2.81/1.44  Demodulation         : 0.05
% 2.81/1.44  BG Simplification    : 0.02
% 2.81/1.44  Subsumption          : 0.05
% 2.81/1.44  Abstraction          : 0.01
% 2.81/1.44  MUC search           : 0.00
% 2.81/1.44  Cooper               : 0.00
% 2.81/1.44  Total                : 0.67
% 2.81/1.44  Index Insertion      : 0.00
% 2.81/1.44  Index Deletion       : 0.00
% 2.81/1.44  Index Matching       : 0.00
% 2.81/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

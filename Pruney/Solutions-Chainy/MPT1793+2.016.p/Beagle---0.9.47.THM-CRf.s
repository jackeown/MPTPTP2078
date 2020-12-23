%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:55 EST 2020

% Result     : Theorem 11.54s
% Output     : CNFRefutation 11.54s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 367 expanded)
%              Number of leaves         :   42 ( 156 expanded)
%              Depth                    :   14
%              Number of atoms          :  282 (1604 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_212,negated_conjecture,(
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

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_84,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_148,axiom,(
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

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_188,axiom,(
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

tff(f_68,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_70,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_110,plain,(
    ! [B_120,A_121] :
      ( l1_pre_topc(B_120)
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_113,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_110])).

tff(c_116,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_113])).

tff(c_28,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_380,plain,(
    ! [C_172,A_173,B_174] :
      ( m1_subset_1(C_172,u1_struct_0(A_173))
      | ~ m1_subset_1(C_172,u1_struct_0(B_174))
      | ~ m1_pre_topc(B_174,A_173)
      | v2_struct_0(B_174)
      | ~ l1_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_382,plain,(
    ! [A_173] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_173))
      | ~ m1_pre_topc('#skF_5',A_173)
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_60,c_380])).

tff(c_385,plain,(
    ! [A_173] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_173))
      | ~ m1_pre_topc('#skF_5',A_173)
      | ~ l1_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_382])).

tff(c_140,plain,(
    ! [A_131,B_132] :
      ( r2_hidden(A_131,B_132)
      | v1_xboole_0(B_132)
      | ~ m1_subset_1(A_131,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    r1_xboole_0(u1_struct_0('#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_84,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(A_115,B_116) = A_115
      | ~ r1_xboole_0(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    k4_xboole_0(u1_struct_0('#skF_5'),'#skF_4') = u1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_84])).

tff(c_117,plain,(
    ! [D_122,B_123,A_124] :
      ( ~ r2_hidden(D_122,B_123)
      | ~ r2_hidden(D_122,k4_xboole_0(A_124,B_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [D_122] :
      ( ~ r2_hidden(D_122,'#skF_4')
      | ~ r2_hidden(D_122,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_117])).

tff(c_154,plain,(
    ! [A_131] :
      ( ~ r2_hidden(A_131,'#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_131,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_140,c_120])).

tff(c_181,plain,(
    ! [A_138] :
      ( ~ r2_hidden(A_138,'#skF_4')
      | ~ m1_subset_1(A_138,u1_struct_0('#skF_5')) ) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_185,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_181])).

tff(c_72,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_54,plain,(
    ! [A_31,B_35,C_37] :
      ( r1_tmap_1(A_31,k6_tmap_1(A_31,B_35),k7_tmap_1(A_31,B_35),C_37)
      | r2_hidden(C_37,B_35)
      | ~ m1_subset_1(C_37,u1_struct_0(A_31))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_44,plain,(
    ! [A_27,B_28] :
      ( v1_funct_2(k7_tmap_1(A_27,B_28),u1_struct_0(A_27),u1_struct_0(k6_tmap_1(A_27,B_28)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_207,plain,(
    ! [A_143,B_144] :
      ( ~ v2_struct_0(k6_tmap_1(A_143,B_144))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_210,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_207])).

tff(c_213,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_210])).

tff(c_214,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_213])).

tff(c_246,plain,(
    ! [A_153,B_154] :
      ( v2_pre_topc(k6_tmap_1(A_153,B_154))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_249,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_246])).

tff(c_252,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_249])).

tff(c_253,plain,(
    v2_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_252])).

tff(c_221,plain,(
    ! [A_146,B_147] :
      ( l1_pre_topc(k6_tmap_1(A_146,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_224,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_221])).

tff(c_227,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_224])).

tff(c_228,plain,(
    l1_pre_topc(k6_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_227])).

tff(c_238,plain,(
    ! [A_151,B_152] :
      ( v1_funct_1(k7_tmap_1(A_151,B_152))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_241,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_238])).

tff(c_244,plain,
    ( v1_funct_1(k7_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_241])).

tff(c_245,plain,(
    v1_funct_1(k7_tmap_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_244])).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k7_tmap_1(A_27,B_28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_27),u1_struct_0(k6_tmap_1(A_27,B_28)))))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2746,plain,(
    ! [B_292,A_288,C_289,D_290,F_291] :
      ( r1_tmap_1(D_290,A_288,k2_tmap_1(B_292,A_288,C_289,D_290),F_291)
      | ~ r1_tmap_1(B_292,A_288,C_289,F_291)
      | ~ m1_subset_1(F_291,u1_struct_0(D_290))
      | ~ m1_subset_1(F_291,u1_struct_0(B_292))
      | ~ m1_pre_topc(D_290,B_292)
      | v2_struct_0(D_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_292),u1_struct_0(A_288))))
      | ~ v1_funct_2(C_289,u1_struct_0(B_292),u1_struct_0(A_288))
      | ~ v1_funct_1(C_289)
      | ~ l1_pre_topc(B_292)
      | ~ v2_pre_topc(B_292)
      | v2_struct_0(B_292)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288)
      | v2_struct_0(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_20753,plain,(
    ! [D_5913,A_5914,B_5915,F_5916] :
      ( r1_tmap_1(D_5913,k6_tmap_1(A_5914,B_5915),k2_tmap_1(A_5914,k6_tmap_1(A_5914,B_5915),k7_tmap_1(A_5914,B_5915),D_5913),F_5916)
      | ~ r1_tmap_1(A_5914,k6_tmap_1(A_5914,B_5915),k7_tmap_1(A_5914,B_5915),F_5916)
      | ~ m1_subset_1(F_5916,u1_struct_0(D_5913))
      | ~ m1_subset_1(F_5916,u1_struct_0(A_5914))
      | ~ m1_pre_topc(D_5913,A_5914)
      | v2_struct_0(D_5913)
      | ~ v1_funct_2(k7_tmap_1(A_5914,B_5915),u1_struct_0(A_5914),u1_struct_0(k6_tmap_1(A_5914,B_5915)))
      | ~ v1_funct_1(k7_tmap_1(A_5914,B_5915))
      | ~ l1_pre_topc(k6_tmap_1(A_5914,B_5915))
      | ~ v2_pre_topc(k6_tmap_1(A_5914,B_5915))
      | v2_struct_0(k6_tmap_1(A_5914,B_5915))
      | ~ m1_subset_1(B_5915,k1_zfmisc_1(u1_struct_0(A_5914)))
      | ~ l1_pre_topc(A_5914)
      | ~ v2_pre_topc(A_5914)
      | v2_struct_0(A_5914) ) ),
    inference(resolution,[status(thm)],[c_42,c_2746])).

tff(c_58,plain,(
    ~ r1_tmap_1('#skF_5',k6_tmap_1('#skF_3','#skF_4'),k2_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_20756,plain,
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
    inference(resolution,[status(thm)],[c_20753,c_58])).

tff(c_20771,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_5')
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4')))
    | v2_struct_0(k6_tmap_1('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_253,c_228,c_245,c_64,c_60,c_20756])).

tff(c_20772,plain,
    ( ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_214,c_66,c_20771])).

tff(c_21160,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_3','#skF_4'),u1_struct_0('#skF_3'),u1_struct_0(k6_tmap_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_20772])).

tff(c_21172,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_21160])).

tff(c_21175,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_21172])).

tff(c_21177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_21175])).

tff(c_21178,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_20772])).

tff(c_21192,plain,(
    ~ r1_tmap_1('#skF_3',k6_tmap_1('#skF_3','#skF_4'),k7_tmap_1('#skF_3','#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_21178])).

tff(c_21201,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_21192])).

tff(c_21204,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_21201])).

tff(c_21205,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_185,c_21204])).

tff(c_21208,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_385,c_21205])).

tff(c_21211,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_21208])).

tff(c_21213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_21211])).

tff(c_21214,plain,(
    ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_21178])).

tff(c_21218,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_385,c_21214])).

tff(c_21221,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_64,c_21218])).

tff(c_21223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_21221])).

tff(c_21224,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_32,plain,(
    ! [A_17] :
      ( ~ v1_xboole_0(u1_struct_0(A_17))
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_21227,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_21224,c_32])).

tff(c_21230,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_21227])).

tff(c_21233,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_21230])).

tff(c_21237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_21233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:14:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.54/4.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.33  
% 11.54/4.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.33  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 11.54/4.33  
% 11.54/4.33  %Foreground sorts:
% 11.54/4.33  
% 11.54/4.33  
% 11.54/4.33  %Background operators:
% 11.54/4.33  
% 11.54/4.33  
% 11.54/4.33  %Foreground operators:
% 11.54/4.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.54/4.33  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 11.54/4.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.54/4.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 11.54/4.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.54/4.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.54/4.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.54/4.33  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 11.54/4.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.54/4.33  tff('#skF_5', type, '#skF_5': $i).
% 11.54/4.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 11.54/4.33  tff('#skF_6', type, '#skF_6': $i).
% 11.54/4.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.54/4.33  tff('#skF_3', type, '#skF_3': $i).
% 11.54/4.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.54/4.33  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 11.54/4.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.54/4.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.54/4.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.54/4.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.54/4.33  tff('#skF_4', type, '#skF_4': $i).
% 11.54/4.33  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 11.54/4.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.54/4.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.54/4.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.54/4.33  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 11.54/4.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.54/4.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.54/4.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.54/4.33  
% 11.54/4.35  tff(f_212, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 11.54/4.35  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.54/4.35  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.54/4.35  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 11.54/4.35  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 11.54/4.35  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 11.54/4.35  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.54/4.35  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 11.54/4.35  tff(f_114, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 11.54/4.35  tff(f_130, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 11.54/4.35  tff(f_99, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 11.54/4.35  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 11.54/4.35  tff(f_68, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 11.54/4.35  tff(c_70, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_110, plain, (![B_120, A_121]: (l1_pre_topc(B_120) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.54/4.35  tff(c_113, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_110])).
% 11.54/4.35  tff(c_116, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_113])).
% 11.54/4.35  tff(c_28, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.54/4.35  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_74, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_380, plain, (![C_172, A_173, B_174]: (m1_subset_1(C_172, u1_struct_0(A_173)) | ~m1_subset_1(C_172, u1_struct_0(B_174)) | ~m1_pre_topc(B_174, A_173) | v2_struct_0(B_174) | ~l1_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.54/4.35  tff(c_382, plain, (![A_173]: (m1_subset_1('#skF_6', u1_struct_0(A_173)) | ~m1_pre_topc('#skF_5', A_173) | v2_struct_0('#skF_5') | ~l1_pre_topc(A_173) | v2_struct_0(A_173))), inference(resolution, [status(thm)], [c_60, c_380])).
% 11.54/4.35  tff(c_385, plain, (![A_173]: (m1_subset_1('#skF_6', u1_struct_0(A_173)) | ~m1_pre_topc('#skF_5', A_173) | ~l1_pre_topc(A_173) | v2_struct_0(A_173))), inference(negUnitSimplification, [status(thm)], [c_66, c_382])).
% 11.54/4.35  tff(c_140, plain, (![A_131, B_132]: (r2_hidden(A_131, B_132) | v1_xboole_0(B_132) | ~m1_subset_1(A_131, B_132))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.54/4.35  tff(c_62, plain, (r1_xboole_0(u1_struct_0('#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_84, plain, (![A_115, B_116]: (k4_xboole_0(A_115, B_116)=A_115 | ~r1_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.54/4.35  tff(c_92, plain, (k4_xboole_0(u1_struct_0('#skF_5'), '#skF_4')=u1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_84])).
% 11.54/4.35  tff(c_117, plain, (![D_122, B_123, A_124]: (~r2_hidden(D_122, B_123) | ~r2_hidden(D_122, k4_xboole_0(A_124, B_123)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.54/4.35  tff(c_120, plain, (![D_122]: (~r2_hidden(D_122, '#skF_4') | ~r2_hidden(D_122, u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_92, c_117])).
% 11.54/4.35  tff(c_154, plain, (![A_131]: (~r2_hidden(A_131, '#skF_4') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_131, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_140, c_120])).
% 11.54/4.35  tff(c_181, plain, (![A_138]: (~r2_hidden(A_138, '#skF_4') | ~m1_subset_1(A_138, u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_154])).
% 11.54/4.35  tff(c_185, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_181])).
% 11.54/4.35  tff(c_72, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_54, plain, (![A_31, B_35, C_37]: (r1_tmap_1(A_31, k6_tmap_1(A_31, B_35), k7_tmap_1(A_31, B_35), C_37) | r2_hidden(C_37, B_35) | ~m1_subset_1(C_37, u1_struct_0(A_31)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_148])).
% 11.54/4.35  tff(c_44, plain, (![A_27, B_28]: (v1_funct_2(k7_tmap_1(A_27, B_28), u1_struct_0(A_27), u1_struct_0(k6_tmap_1(A_27, B_28))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.54/4.35  tff(c_207, plain, (![A_143, B_144]: (~v2_struct_0(k6_tmap_1(A_143, B_144)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.54/4.35  tff(c_210, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_207])).
% 11.54/4.35  tff(c_213, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_210])).
% 11.54/4.35  tff(c_214, plain, (~v2_struct_0(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_213])).
% 11.54/4.35  tff(c_246, plain, (![A_153, B_154]: (v2_pre_topc(k6_tmap_1(A_153, B_154)) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.54/4.35  tff(c_249, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_246])).
% 11.54/4.35  tff(c_252, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_249])).
% 11.54/4.35  tff(c_253, plain, (v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_252])).
% 11.54/4.35  tff(c_221, plain, (![A_146, B_147]: (l1_pre_topc(k6_tmap_1(A_146, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.54/4.35  tff(c_224, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_221])).
% 11.54/4.35  tff(c_227, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_224])).
% 11.54/4.35  tff(c_228, plain, (l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_227])).
% 11.54/4.35  tff(c_238, plain, (![A_151, B_152]: (v1_funct_1(k7_tmap_1(A_151, B_152)) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.54/4.35  tff(c_241, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_68, c_238])).
% 11.54/4.35  tff(c_244, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_241])).
% 11.54/4.35  tff(c_245, plain, (v1_funct_1(k7_tmap_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_244])).
% 11.54/4.35  tff(c_42, plain, (![A_27, B_28]: (m1_subset_1(k7_tmap_1(A_27, B_28), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_27), u1_struct_0(k6_tmap_1(A_27, B_28))))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.54/4.35  tff(c_2746, plain, (![B_292, A_288, C_289, D_290, F_291]: (r1_tmap_1(D_290, A_288, k2_tmap_1(B_292, A_288, C_289, D_290), F_291) | ~r1_tmap_1(B_292, A_288, C_289, F_291) | ~m1_subset_1(F_291, u1_struct_0(D_290)) | ~m1_subset_1(F_291, u1_struct_0(B_292)) | ~m1_pre_topc(D_290, B_292) | v2_struct_0(D_290) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_292), u1_struct_0(A_288)))) | ~v1_funct_2(C_289, u1_struct_0(B_292), u1_struct_0(A_288)) | ~v1_funct_1(C_289) | ~l1_pre_topc(B_292) | ~v2_pre_topc(B_292) | v2_struct_0(B_292) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288) | v2_struct_0(A_288))), inference(cnfTransformation, [status(thm)], [f_188])).
% 11.54/4.35  tff(c_20753, plain, (![D_5913, A_5914, B_5915, F_5916]: (r1_tmap_1(D_5913, k6_tmap_1(A_5914, B_5915), k2_tmap_1(A_5914, k6_tmap_1(A_5914, B_5915), k7_tmap_1(A_5914, B_5915), D_5913), F_5916) | ~r1_tmap_1(A_5914, k6_tmap_1(A_5914, B_5915), k7_tmap_1(A_5914, B_5915), F_5916) | ~m1_subset_1(F_5916, u1_struct_0(D_5913)) | ~m1_subset_1(F_5916, u1_struct_0(A_5914)) | ~m1_pre_topc(D_5913, A_5914) | v2_struct_0(D_5913) | ~v1_funct_2(k7_tmap_1(A_5914, B_5915), u1_struct_0(A_5914), u1_struct_0(k6_tmap_1(A_5914, B_5915))) | ~v1_funct_1(k7_tmap_1(A_5914, B_5915)) | ~l1_pre_topc(k6_tmap_1(A_5914, B_5915)) | ~v2_pre_topc(k6_tmap_1(A_5914, B_5915)) | v2_struct_0(k6_tmap_1(A_5914, B_5915)) | ~m1_subset_1(B_5915, k1_zfmisc_1(u1_struct_0(A_5914))) | ~l1_pre_topc(A_5914) | ~v2_pre_topc(A_5914) | v2_struct_0(A_5914))), inference(resolution, [status(thm)], [c_42, c_2746])).
% 11.54/4.35  tff(c_58, plain, (~r1_tmap_1('#skF_5', k6_tmap_1('#skF_3', '#skF_4'), k2_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_212])).
% 11.54/4.35  tff(c_20756, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | ~v1_funct_1(k7_tmap_1('#skF_3', '#skF_4')) | ~l1_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | ~v2_pre_topc(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_20753, c_58])).
% 11.54/4.35  tff(c_20771, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_5') | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4'))) | v2_struct_0(k6_tmap_1('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_253, c_228, c_245, c_64, c_60, c_20756])).
% 11.54/4.35  tff(c_20772, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_74, c_214, c_66, c_20771])).
% 11.54/4.35  tff(c_21160, plain, (~v1_funct_2(k7_tmap_1('#skF_3', '#skF_4'), u1_struct_0('#skF_3'), u1_struct_0(k6_tmap_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_20772])).
% 11.54/4.35  tff(c_21172, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_21160])).
% 11.54/4.35  tff(c_21175, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_21172])).
% 11.54/4.35  tff(c_21177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_21175])).
% 11.54/4.35  tff(c_21178, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitRight, [status(thm)], [c_20772])).
% 11.54/4.35  tff(c_21192, plain, (~r1_tmap_1('#skF_3', k6_tmap_1('#skF_3', '#skF_4'), k7_tmap_1('#skF_3', '#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_21178])).
% 11.54/4.35  tff(c_21201, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_54, c_21192])).
% 11.54/4.35  tff(c_21204, plain, (r2_hidden('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_21201])).
% 11.54/4.35  tff(c_21205, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_185, c_21204])).
% 11.54/4.35  tff(c_21208, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_385, c_21205])).
% 11.54/4.35  tff(c_21211, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_21208])).
% 11.54/4.35  tff(c_21213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_21211])).
% 11.54/4.35  tff(c_21214, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_21178])).
% 11.54/4.35  tff(c_21218, plain, (~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_385, c_21214])).
% 11.54/4.35  tff(c_21221, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_64, c_21218])).
% 11.54/4.35  tff(c_21223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_21221])).
% 11.54/4.35  tff(c_21224, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_154])).
% 11.54/4.35  tff(c_32, plain, (![A_17]: (~v1_xboole_0(u1_struct_0(A_17)) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.54/4.35  tff(c_21227, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_21224, c_32])).
% 11.54/4.35  tff(c_21230, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_21227])).
% 11.54/4.35  tff(c_21233, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_28, c_21230])).
% 11.54/4.35  tff(c_21237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_21233])).
% 11.54/4.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.54/4.35  
% 11.54/4.35  Inference rules
% 11.54/4.35  ----------------------
% 11.54/4.35  #Ref     : 4
% 11.54/4.35  #Sup     : 4825
% 11.54/4.35  #Fact    : 0
% 11.54/4.35  #Define  : 0
% 11.54/4.35  #Split   : 14
% 11.54/4.35  #Chain   : 0
% 11.54/4.35  #Close   : 0
% 11.54/4.35  
% 11.54/4.35  Ordering : KBO
% 11.54/4.35  
% 11.54/4.35  Simplification rules
% 11.54/4.35  ----------------------
% 11.54/4.35  #Subsume      : 1474
% 11.54/4.35  #Demod        : 1228
% 11.54/4.35  #Tautology    : 490
% 11.54/4.35  #SimpNegUnit  : 20
% 11.54/4.35  #BackRed      : 0
% 11.54/4.35  
% 11.54/4.35  #Partial instantiations: 3614
% 11.54/4.35  #Strategies tried      : 1
% 11.54/4.35  
% 11.54/4.35  Timing (in seconds)
% 11.54/4.35  ----------------------
% 11.54/4.35  Preprocessing        : 0.43
% 11.54/4.35  Parsing              : 0.23
% 11.54/4.35  CNF conversion       : 0.04
% 11.54/4.35  Main loop            : 3.13
% 11.54/4.35  Inferencing          : 0.79
% 11.54/4.35  Reduction            : 1.23
% 11.54/4.35  Demodulation         : 1.03
% 11.54/4.35  BG Simplification    : 0.11
% 11.54/4.35  Subsumption          : 0.85
% 11.54/4.35  Abstraction          : 0.12
% 11.54/4.35  MUC search           : 0.00
% 11.54/4.35  Cooper               : 0.00
% 11.54/4.35  Total                : 3.60
% 11.54/4.35  Index Insertion      : 0.00
% 11.54/4.35  Index Deletion       : 0.00
% 11.54/4.35  Index Matching       : 0.00
% 11.54/4.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

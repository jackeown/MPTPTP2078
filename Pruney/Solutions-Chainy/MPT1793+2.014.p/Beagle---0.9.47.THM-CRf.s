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
% DateTime   : Thu Dec  3 10:27:55 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 3.03s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 419 expanded)
%              Number of leaves         :   43 ( 172 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 (1787 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_228,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_100,axiom,(
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

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_49,axiom,(
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

tff(f_164,axiom,(
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

tff(f_130,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_funct_1(k7_tmap_1(A,B))
        & v1_funct_2(k7_tmap_1(A,B),u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B)))
        & m1_subset_1(k7_tmap_1(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(k6_tmap_1(A,B))))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( ~ v2_struct_0(k6_tmap_1(A,B))
        & v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_204,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_struct_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_72,plain,(
    ! [B_119,A_120] :
      ( l1_pre_topc(B_119)
      | ~ m1_pre_topc(B_119,A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_72])).

tff(c_78,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_75])).

tff(c_16,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_275,plain,(
    ! [C_165,A_166,B_167] :
      ( m1_subset_1(C_165,u1_struct_0(A_166))
      | ~ m1_subset_1(C_165,u1_struct_0(B_167))
      | ~ m1_pre_topc(B_167,A_166)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_277,plain,(
    ! [A_166] :
      ( m1_subset_1('#skF_7',u1_struct_0(A_166))
      | ~ m1_pre_topc('#skF_6',A_166)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_50,c_275])).

tff(c_280,plain,(
    ! [A_166] :
      ( m1_subset_1('#skF_7',u1_struct_0(A_166))
      | ~ m1_pre_topc('#skF_6',A_166)
      | ~ l1_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_277])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_hidden(A_10,B_11)
      | v1_xboole_0(B_11)
      | ~ m1_subset_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_52,plain,(
    r1_xboole_0(u1_struct_0('#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_102,plain,(
    ! [A_135,B_136,C_137] :
      ( ~ r1_xboole_0(A_135,B_136)
      | ~ r2_hidden(C_137,B_136)
      | ~ r2_hidden(C_137,A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [C_138] :
      ( ~ r2_hidden(C_138,'#skF_5')
      | ~ r2_hidden(C_138,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_52,c_102])).

tff(c_130,plain,(
    ! [A_10] :
      ( ~ r2_hidden(A_10,'#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_6'))
      | ~ m1_subset_1(A_10,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_12,c_112])).

tff(c_155,plain,(
    ! [A_141] :
      ( ~ r2_hidden(A_141,'#skF_5')
      | ~ m1_subset_1(A_141,u1_struct_0('#skF_6')) ) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_159,plain,(
    ~ r2_hidden('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_155])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_44,plain,(
    ! [A_34,B_38,C_40] :
      ( r1_tmap_1(A_34,k6_tmap_1(A_34,B_38),k7_tmap_1(A_34,B_38),C_40)
      | r2_hidden(C_40,B_38)
      | ~ m1_subset_1(C_40,u1_struct_0(A_34))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( v1_funct_2(k7_tmap_1(A_30,B_31),u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_221,plain,(
    ! [A_152,B_153] :
      ( ~ v2_struct_0(k6_tmap_1(A_152,B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_227,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_221])).

tff(c_231,plain,
    ( ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_227])).

tff(c_232,plain,(
    ~ v2_struct_0(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_231])).

tff(c_165,plain,(
    ! [A_142,B_143] :
      ( v2_pre_topc(k6_tmap_1(A_142,B_143))
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_171,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_165])).

tff(c_175,plain,
    ( v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_171])).

tff(c_176,plain,(
    v2_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_175])).

tff(c_262,plain,(
    ! [A_162,B_163] :
      ( l1_pre_topc(k6_tmap_1(A_162,B_163))
      | ~ m1_subset_1(B_163,k1_zfmisc_1(u1_struct_0(A_162)))
      | ~ l1_pre_topc(A_162)
      | ~ v2_pre_topc(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_268,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_262])).

tff(c_272,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_268])).

tff(c_273,plain,(
    l1_pre_topc(k6_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_272])).

tff(c_249,plain,(
    ! [A_159,B_160] :
      ( v1_funct_1(k7_tmap_1(A_159,B_160))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(u1_struct_0(A_159)))
      | ~ l1_pre_topc(A_159)
      | ~ v2_pre_topc(A_159)
      | v2_struct_0(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_255,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_249])).

tff(c_259,plain,
    ( v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_255])).

tff(c_260,plain,(
    v1_funct_1(k7_tmap_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_259])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k7_tmap_1(A_30,B_31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30),u1_struct_0(k6_tmap_1(A_30,B_31)))))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_308,plain,(
    ! [A_181,C_184,F_183,B_182,D_185] :
      ( r1_tmap_1(D_185,A_181,k2_tmap_1(B_182,A_181,C_184,D_185),F_183)
      | ~ r1_tmap_1(B_182,A_181,C_184,F_183)
      | ~ m1_subset_1(F_183,u1_struct_0(D_185))
      | ~ m1_subset_1(F_183,u1_struct_0(B_182))
      | ~ m1_pre_topc(D_185,B_182)
      | v2_struct_0(D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_182),u1_struct_0(A_181))))
      | ~ v1_funct_2(C_184,u1_struct_0(B_182),u1_struct_0(A_181))
      | ~ v1_funct_1(C_184)
      | ~ l1_pre_topc(B_182)
      | ~ v2_pre_topc(B_182)
      | v2_struct_0(B_182)
      | ~ l1_pre_topc(A_181)
      | ~ v2_pre_topc(A_181)
      | v2_struct_0(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_312,plain,(
    ! [D_186,A_187,B_188,F_189] :
      ( r1_tmap_1(D_186,k6_tmap_1(A_187,B_188),k2_tmap_1(A_187,k6_tmap_1(A_187,B_188),k7_tmap_1(A_187,B_188),D_186),F_189)
      | ~ r1_tmap_1(A_187,k6_tmap_1(A_187,B_188),k7_tmap_1(A_187,B_188),F_189)
      | ~ m1_subset_1(F_189,u1_struct_0(D_186))
      | ~ m1_subset_1(F_189,u1_struct_0(A_187))
      | ~ m1_pre_topc(D_186,A_187)
      | v2_struct_0(D_186)
      | ~ v1_funct_2(k7_tmap_1(A_187,B_188),u1_struct_0(A_187),u1_struct_0(k6_tmap_1(A_187,B_188)))
      | ~ v1_funct_1(k7_tmap_1(A_187,B_188))
      | ~ l1_pre_topc(k6_tmap_1(A_187,B_188))
      | ~ v2_pre_topc(k6_tmap_1(A_187,B_188))
      | v2_struct_0(k6_tmap_1(A_187,B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_32,c_308])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_6',k6_tmap_1('#skF_4','#skF_5'),k2_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_315,plain,
    ( ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | ~ v1_funct_1(k7_tmap_1('#skF_4','#skF_5'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | ~ v2_pre_topc(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_312,c_48])).

tff(c_318,plain,
    ( ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_6')
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5')))
    | v2_struct_0(k6_tmap_1('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_176,c_273,c_260,c_54,c_50,c_315])).

tff(c_319,plain,
    ( ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_232,c_56,c_318])).

tff(c_320,plain,(
    ~ v1_funct_2(k7_tmap_1('#skF_4','#skF_5'),u1_struct_0('#skF_4'),u1_struct_0(k6_tmap_1('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_319])).

tff(c_323,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_320])).

tff(c_326,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_323])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_326])).

tff(c_329,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_319])).

tff(c_331,plain,(
    ~ r1_tmap_1('#skF_4',k6_tmap_1('#skF_4','#skF_5'),k7_tmap_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_334,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_331])).

tff(c_337,plain,
    ( r2_hidden('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_334])).

tff(c_338,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_159,c_337])).

tff(c_341,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_280,c_338])).

tff(c_344,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_341])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_344])).

tff(c_347,plain,(
    ~ m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_351,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_280,c_347])).

tff(c_354,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_54,c_351])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_354])).

tff(c_357,plain,(
    v1_xboole_0(u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [A_139] :
      ( m1_subset_1('#skF_3'(A_139),k1_zfmisc_1(u1_struct_0(A_139)))
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_371,plain,(
    ! [A_191,A_192] :
      ( ~ v1_xboole_0(u1_struct_0(A_191))
      | ~ r2_hidden(A_192,'#skF_3'(A_191))
      | ~ l1_struct_0(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_133,c_14])).

tff(c_392,plain,(
    ! [A_193] :
      ( ~ v1_xboole_0(u1_struct_0(A_193))
      | ~ l1_struct_0(A_193)
      | v2_struct_0(A_193)
      | v1_xboole_0('#skF_3'(A_193)) ) ),
    inference(resolution,[status(thm)],[c_4,c_371])).

tff(c_395,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6')
    | v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_357,c_392])).

tff(c_398,plain,
    ( ~ l1_struct_0('#skF_6')
    | v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_395])).

tff(c_399,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_398])).

tff(c_414,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_399])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_414])).

tff(c_420,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_419,plain,(
    v1_xboole_0('#skF_3'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_398])).

tff(c_20,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_3'(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_423,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_419,c_20])).

tff(c_426,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_423])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.32  % Computer   : n009.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 13:11:41 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.38  %$ r1_tmap_1 > v1_funct_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k7_tmap_1 > k6_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 2.73/1.38  
% 2.73/1.38  %Foreground sorts:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Background operators:
% 2.73/1.38  
% 2.73/1.38  
% 2.73/1.38  %Foreground operators:
% 2.73/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.38  tff(k7_tmap_1, type, k7_tmap_1: ($i * $i) > $i).
% 2.73/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.38  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.73/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.73/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.73/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.73/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.38  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.73/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.38  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.73/1.38  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.73/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.73/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.73/1.38  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 2.73/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.38  
% 3.03/1.40  tff(f_228, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_xboole_0(u1_struct_0(C), B) => (![D]: (m1_subset_1(D, u1_struct_0(C)) => r1_tmap_1(C, k6_tmap_1(A, B), k2_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_tmap_1)).
% 3.03/1.40  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.03/1.40  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.03/1.40  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => m1_subset_1(C, u1_struct_0(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_pre_topc)).
% 3.03/1.40  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.03/1.40  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.03/1.40  tff(f_164, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (~r2_hidden(C, B) => r1_tmap_1(A, k6_tmap_1(A, B), k7_tmap_1(A, B), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_tmap_1)).
% 3.03/1.40  tff(f_130, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_funct_1(k7_tmap_1(A, B)) & v1_funct_2(k7_tmap_1(A, B), u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))) & m1_subset_1(k7_tmap_1(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(k6_tmap_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 3.03/1.40  tff(f_146, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((~v2_struct_0(k6_tmap_1(A, B)) & v1_pre_topc(k6_tmap_1(A, B))) & v2_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tmap_1)).
% 3.03/1.40  tff(f_115, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 3.03/1.40  tff(f_204, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 3.03/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.03/1.40  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc4_struct_0)).
% 3.03/1.40  tff(f_62, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.03/1.40  tff(c_56, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_72, plain, (![B_119, A_120]: (l1_pre_topc(B_119) | ~m1_pre_topc(B_119, A_120) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.03/1.40  tff(c_75, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_72])).
% 3.03/1.40  tff(c_78, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_75])).
% 3.03/1.40  tff(c_16, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.03/1.40  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_275, plain, (![C_165, A_166, B_167]: (m1_subset_1(C_165, u1_struct_0(A_166)) | ~m1_subset_1(C_165, u1_struct_0(B_167)) | ~m1_pre_topc(B_167, A_166) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.03/1.40  tff(c_277, plain, (![A_166]: (m1_subset_1('#skF_7', u1_struct_0(A_166)) | ~m1_pre_topc('#skF_6', A_166) | v2_struct_0('#skF_6') | ~l1_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_50, c_275])).
% 3.03/1.40  tff(c_280, plain, (![A_166]: (m1_subset_1('#skF_7', u1_struct_0(A_166)) | ~m1_pre_topc('#skF_6', A_166) | ~l1_pre_topc(A_166) | v2_struct_0(A_166))), inference(negUnitSimplification, [status(thm)], [c_56, c_277])).
% 3.03/1.40  tff(c_12, plain, (![A_10, B_11]: (r2_hidden(A_10, B_11) | v1_xboole_0(B_11) | ~m1_subset_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.03/1.40  tff(c_52, plain, (r1_xboole_0(u1_struct_0('#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_102, plain, (![A_135, B_136, C_137]: (~r1_xboole_0(A_135, B_136) | ~r2_hidden(C_137, B_136) | ~r2_hidden(C_137, A_135))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.03/1.40  tff(c_112, plain, (![C_138]: (~r2_hidden(C_138, '#skF_5') | ~r2_hidden(C_138, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_52, c_102])).
% 3.03/1.40  tff(c_130, plain, (![A_10]: (~r2_hidden(A_10, '#skF_5') | v1_xboole_0(u1_struct_0('#skF_6')) | ~m1_subset_1(A_10, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_12, c_112])).
% 3.03/1.40  tff(c_155, plain, (![A_141]: (~r2_hidden(A_141, '#skF_5') | ~m1_subset_1(A_141, u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_130])).
% 3.03/1.40  tff(c_159, plain, (~r2_hidden('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_155])).
% 3.03/1.40  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_44, plain, (![A_34, B_38, C_40]: (r1_tmap_1(A_34, k6_tmap_1(A_34, B_38), k7_tmap_1(A_34, B_38), C_40) | r2_hidden(C_40, B_38) | ~m1_subset_1(C_40, u1_struct_0(A_34)) | ~m1_subset_1(B_38, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_164])).
% 3.03/1.40  tff(c_34, plain, (![A_30, B_31]: (v1_funct_2(k7_tmap_1(A_30, B_31), u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.03/1.40  tff(c_221, plain, (![A_152, B_153]: (~v2_struct_0(k6_tmap_1(A_152, B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.03/1.40  tff(c_227, plain, (~v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_221])).
% 3.03/1.40  tff(c_231, plain, (~v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_227])).
% 3.03/1.40  tff(c_232, plain, (~v2_struct_0(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_231])).
% 3.03/1.40  tff(c_165, plain, (![A_142, B_143]: (v2_pre_topc(k6_tmap_1(A_142, B_143)) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.03/1.40  tff(c_171, plain, (v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_165])).
% 3.03/1.40  tff(c_175, plain, (v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_171])).
% 3.03/1.40  tff(c_176, plain, (v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_175])).
% 3.03/1.40  tff(c_262, plain, (![A_162, B_163]: (l1_pre_topc(k6_tmap_1(A_162, B_163)) | ~m1_subset_1(B_163, k1_zfmisc_1(u1_struct_0(A_162))) | ~l1_pre_topc(A_162) | ~v2_pre_topc(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.03/1.40  tff(c_268, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_262])).
% 3.03/1.40  tff(c_272, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_268])).
% 3.03/1.40  tff(c_273, plain, (l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_272])).
% 3.03/1.40  tff(c_249, plain, (![A_159, B_160]: (v1_funct_1(k7_tmap_1(A_159, B_160)) | ~m1_subset_1(B_160, k1_zfmisc_1(u1_struct_0(A_159))) | ~l1_pre_topc(A_159) | ~v2_pre_topc(A_159) | v2_struct_0(A_159))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.03/1.40  tff(c_255, plain, (v1_funct_1(k7_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_249])).
% 3.03/1.40  tff(c_259, plain, (v1_funct_1(k7_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_255])).
% 3.03/1.40  tff(c_260, plain, (v1_funct_1(k7_tmap_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_64, c_259])).
% 3.03/1.40  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(k7_tmap_1(A_30, B_31), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_30), u1_struct_0(k6_tmap_1(A_30, B_31))))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_30))) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.03/1.40  tff(c_308, plain, (![A_181, C_184, F_183, B_182, D_185]: (r1_tmap_1(D_185, A_181, k2_tmap_1(B_182, A_181, C_184, D_185), F_183) | ~r1_tmap_1(B_182, A_181, C_184, F_183) | ~m1_subset_1(F_183, u1_struct_0(D_185)) | ~m1_subset_1(F_183, u1_struct_0(B_182)) | ~m1_pre_topc(D_185, B_182) | v2_struct_0(D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_182), u1_struct_0(A_181)))) | ~v1_funct_2(C_184, u1_struct_0(B_182), u1_struct_0(A_181)) | ~v1_funct_1(C_184) | ~l1_pre_topc(B_182) | ~v2_pre_topc(B_182) | v2_struct_0(B_182) | ~l1_pre_topc(A_181) | ~v2_pre_topc(A_181) | v2_struct_0(A_181))), inference(cnfTransformation, [status(thm)], [f_204])).
% 3.03/1.40  tff(c_312, plain, (![D_186, A_187, B_188, F_189]: (r1_tmap_1(D_186, k6_tmap_1(A_187, B_188), k2_tmap_1(A_187, k6_tmap_1(A_187, B_188), k7_tmap_1(A_187, B_188), D_186), F_189) | ~r1_tmap_1(A_187, k6_tmap_1(A_187, B_188), k7_tmap_1(A_187, B_188), F_189) | ~m1_subset_1(F_189, u1_struct_0(D_186)) | ~m1_subset_1(F_189, u1_struct_0(A_187)) | ~m1_pre_topc(D_186, A_187) | v2_struct_0(D_186) | ~v1_funct_2(k7_tmap_1(A_187, B_188), u1_struct_0(A_187), u1_struct_0(k6_tmap_1(A_187, B_188))) | ~v1_funct_1(k7_tmap_1(A_187, B_188)) | ~l1_pre_topc(k6_tmap_1(A_187, B_188)) | ~v2_pre_topc(k6_tmap_1(A_187, B_188)) | v2_struct_0(k6_tmap_1(A_187, B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0(A_187))) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(resolution, [status(thm)], [c_32, c_308])).
% 3.03/1.40  tff(c_48, plain, (~r1_tmap_1('#skF_6', k6_tmap_1('#skF_4', '#skF_5'), k2_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_228])).
% 3.03/1.40  tff(c_315, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5'))) | ~v1_funct_1(k7_tmap_1('#skF_4', '#skF_5')) | ~l1_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | ~v2_pre_topc(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_312, c_48])).
% 3.03/1.40  tff(c_318, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | v2_struct_0('#skF_6') | ~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5'))) | v2_struct_0(k6_tmap_1('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_176, c_273, c_260, c_54, c_50, c_315])).
% 3.03/1.40  tff(c_319, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_232, c_56, c_318])).
% 3.03/1.40  tff(c_320, plain, (~v1_funct_2(k7_tmap_1('#skF_4', '#skF_5'), u1_struct_0('#skF_4'), u1_struct_0(k6_tmap_1('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_319])).
% 3.03/1.40  tff(c_323, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_34, c_320])).
% 3.03/1.40  tff(c_326, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_323])).
% 3.03/1.40  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_326])).
% 3.03/1.40  tff(c_329, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_319])).
% 3.03/1.40  tff(c_331, plain, (~r1_tmap_1('#skF_4', k6_tmap_1('#skF_4', '#skF_5'), k7_tmap_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_329])).
% 3.03/1.40  tff(c_334, plain, (r2_hidden('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_44, c_331])).
% 3.03/1.40  tff(c_337, plain, (r2_hidden('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_4')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_334])).
% 3.03/1.40  tff(c_338, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_64, c_159, c_337])).
% 3.03/1.40  tff(c_341, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_280, c_338])).
% 3.03/1.40  tff(c_344, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_341])).
% 3.03/1.40  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_344])).
% 3.03/1.40  tff(c_347, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_329])).
% 3.03/1.40  tff(c_351, plain, (~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_280, c_347])).
% 3.03/1.40  tff(c_354, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_54, c_351])).
% 3.03/1.40  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_354])).
% 3.03/1.40  tff(c_357, plain, (v1_xboole_0(u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_130])).
% 3.03/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.03/1.40  tff(c_133, plain, (![A_139]: (m1_subset_1('#skF_3'(A_139), k1_zfmisc_1(u1_struct_0(A_139))) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.03/1.40  tff(c_14, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.03/1.40  tff(c_371, plain, (![A_191, A_192]: (~v1_xboole_0(u1_struct_0(A_191)) | ~r2_hidden(A_192, '#skF_3'(A_191)) | ~l1_struct_0(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_133, c_14])).
% 3.03/1.40  tff(c_392, plain, (![A_193]: (~v1_xboole_0(u1_struct_0(A_193)) | ~l1_struct_0(A_193) | v2_struct_0(A_193) | v1_xboole_0('#skF_3'(A_193)))), inference(resolution, [status(thm)], [c_4, c_371])).
% 3.03/1.40  tff(c_395, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | v1_xboole_0('#skF_3'('#skF_6'))), inference(resolution, [status(thm)], [c_357, c_392])).
% 3.03/1.40  tff(c_398, plain, (~l1_struct_0('#skF_6') | v1_xboole_0('#skF_3'('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_395])).
% 3.03/1.40  tff(c_399, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_398])).
% 3.03/1.40  tff(c_414, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_16, c_399])).
% 3.03/1.40  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_414])).
% 3.03/1.40  tff(c_420, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_398])).
% 3.03/1.40  tff(c_419, plain, (v1_xboole_0('#skF_3'('#skF_6'))), inference(splitRight, [status(thm)], [c_398])).
% 3.03/1.40  tff(c_20, plain, (![A_19]: (~v1_xboole_0('#skF_3'(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.03/1.40  tff(c_423, plain, (~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_419, c_20])).
% 3.03/1.40  tff(c_426, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_420, c_423])).
% 3.03/1.40  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_426])).
% 3.03/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.03/1.40  
% 3.03/1.40  Inference rules
% 3.03/1.40  ----------------------
% 3.03/1.40  #Ref     : 0
% 3.03/1.40  #Sup     : 61
% 3.03/1.40  #Fact    : 0
% 3.03/1.40  #Define  : 0
% 3.03/1.40  #Split   : 10
% 3.03/1.40  #Chain   : 0
% 3.03/1.40  #Close   : 0
% 3.03/1.40  
% 3.03/1.40  Ordering : KBO
% 3.03/1.40  
% 3.03/1.40  Simplification rules
% 3.03/1.40  ----------------------
% 3.03/1.40  #Subsume      : 10
% 3.03/1.40  #Demod        : 38
% 3.03/1.40  #Tautology    : 4
% 3.03/1.40  #SimpNegUnit  : 16
% 3.03/1.40  #BackRed      : 0
% 3.03/1.40  
% 3.03/1.40  #Partial instantiations: 0
% 3.03/1.40  #Strategies tried      : 1
% 3.03/1.40  
% 3.03/1.40  Timing (in seconds)
% 3.03/1.40  ----------------------
% 3.03/1.41  Preprocessing        : 0.35
% 3.03/1.41  Parsing              : 0.19
% 3.03/1.41  CNF conversion       : 0.03
% 3.03/1.41  Main loop            : 0.31
% 3.03/1.41  Inferencing          : 0.12
% 3.03/1.41  Reduction            : 0.09
% 3.03/1.41  Demodulation         : 0.06
% 3.03/1.41  BG Simplification    : 0.02
% 3.03/1.41  Subsumption          : 0.07
% 3.03/1.41  Abstraction          : 0.01
% 3.03/1.41  MUC search           : 0.00
% 3.03/1.41  Cooper               : 0.00
% 3.03/1.41  Total                : 0.71
% 3.03/1.41  Index Insertion      : 0.00
% 3.03/1.41  Index Deletion       : 0.00
% 3.03/1.41  Index Matching       : 0.00
% 3.03/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:13 EST 2020

% Result     : Theorem 10.18s
% Output     : CNFRefutation 10.18s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 425 expanded)
%              Number of leaves         :   31 ( 179 expanded)
%              Depth                    :   17
%              Number of atoms          :  205 (1663 expanded)
%              Number of equality atoms :    9 (  67 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k3_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_58,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_238,plain,(
    ! [A_102,B_103,C_104] :
      ( '#skF_3'(A_102,B_103,C_104) = C_104
      | ~ m1_subset_1(C_104,u1_struct_0(k9_yellow_6(A_102,B_103)))
      | ~ m1_subset_1(B_103,u1_struct_0(A_102))
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_248,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_238])).

tff(c_256,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_248])).

tff(c_257,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_256])).

tff(c_341,plain,(
    ! [B_118,A_119,C_120] :
      ( r2_hidden(B_118,'#skF_3'(A_119,B_118,C_120))
      | ~ m1_subset_1(C_120,u1_struct_0(k9_yellow_6(A_119,B_118)))
      | ~ m1_subset_1(B_118,u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_357,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_341])).

tff(c_368,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_257,c_357])).

tff(c_369,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_368])).

tff(c_50,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_245,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_238])).

tff(c_252,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_245])).

tff(c_253,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_252])).

tff(c_355,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_341])).

tff(c_364,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_253,c_355])).

tff(c_365,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_364])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_932,plain,(
    ! [A_169,B_170,C_171] :
      ( m1_subset_1('#skF_3'(A_169,B_170,C_171),k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ m1_subset_1(C_171,u1_struct_0(k9_yellow_6(A_169,B_170)))
      | ~ m1_subset_1(B_170,u1_struct_0(A_169))
      | ~ l1_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_940,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_932])).

tff(c_947,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_940])).

tff(c_948,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_947])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_958,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_948,c_26])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k3_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_281,plain,(
    ! [A_107,B_108,C_109] :
      ( v3_pre_topc('#skF_3'(A_107,B_108,C_109),A_107)
      | ~ m1_subset_1(C_109,u1_struct_0(k9_yellow_6(A_107,B_108)))
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_291,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_281])).

tff(c_300,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_257,c_291])).

tff(c_301,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_300])).

tff(c_289,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_281])).

tff(c_296,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_253,c_289])).

tff(c_297,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_296])).

tff(c_943,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_932])).

tff(c_950,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_50,c_943])).

tff(c_951,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_950])).

tff(c_1172,plain,(
    ! [B_187,C_188,A_189] :
      ( v3_pre_topc(k3_xboole_0(B_187,C_188),A_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ v3_pre_topc(C_188,A_189)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ v3_pre_topc(B_187,A_189)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1174,plain,(
    ! [B_187] :
      ( v3_pre_topc(k3_xboole_0(B_187,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_187,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_951,c_1172])).

tff(c_1238,plain,(
    ! [B_190] :
      ( v3_pre_topc(k3_xboole_0(B_190,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_190,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_297,c_1174])).

tff(c_1244,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_948,c_1238])).

tff(c_1306,plain,(
    v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_1244])).

tff(c_1417,plain,(
    ! [C_193,A_194,B_195] :
      ( r2_hidden(C_193,u1_struct_0(k9_yellow_6(A_194,B_195)))
      | ~ v3_pre_topc(C_193,A_194)
      | ~ r2_hidden(B_195,C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ m1_subset_1(B_195,u1_struct_0(A_194))
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9842,plain,(
    ! [C_573,A_574,B_575] :
      ( m1_subset_1(C_573,u1_struct_0(k9_yellow_6(A_574,B_575)))
      | ~ v3_pre_topc(C_573,A_574)
      | ~ r2_hidden(B_575,C_573)
      | ~ m1_subset_1(C_573,k1_zfmisc_1(u1_struct_0(A_574)))
      | ~ m1_subset_1(B_575,u1_struct_0(A_574))
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(resolution,[status(thm)],[c_1417,c_24])).

tff(c_48,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_9852,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_9842,c_48])).

tff(c_9858,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1306,c_9852])).

tff(c_9859,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_9858])).

tff(c_9860,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_9859])).

tff(c_9864,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_9860])).

tff(c_9867,plain,(
    ~ r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_20,c_9864])).

tff(c_9871,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_958,c_9867])).

tff(c_9872,plain,(
    ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_9859])).

tff(c_9876,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_9872])).

tff(c_9880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_365,c_9876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:18:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.18/3.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.43  
% 10.18/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.44  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 10.18/3.44  
% 10.18/3.44  %Foreground sorts:
% 10.18/3.44  
% 10.18/3.44  
% 10.18/3.44  %Background operators:
% 10.18/3.44  
% 10.18/3.44  
% 10.18/3.44  %Foreground operators:
% 10.18/3.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.18/3.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.18/3.44  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 10.18/3.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.18/3.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.18/3.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.18/3.44  tff('#skF_7', type, '#skF_7': $i).
% 10.18/3.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.18/3.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.18/3.44  tff('#skF_5', type, '#skF_5': $i).
% 10.18/3.44  tff('#skF_6', type, '#skF_6': $i).
% 10.18/3.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.18/3.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.18/3.44  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 10.18/3.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.18/3.44  tff('#skF_4', type, '#skF_4': $i).
% 10.18/3.44  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 10.18/3.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.18/3.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.18/3.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.18/3.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.18/3.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.18/3.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.18/3.44  
% 10.18/3.45  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_9)).
% 10.18/3.45  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 10.18/3.45  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 10.18/3.45  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.18/3.45  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 10.18/3.45  tff(f_68, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 10.18/3.45  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 10.18/3.45  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 10.18/3.45  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.18/3.45  tff(c_58, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.18/3.45  tff(c_56, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.18/3.45  tff(c_54, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.18/3.45  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.18/3.45  tff(c_238, plain, (![A_102, B_103, C_104]: ('#skF_3'(A_102, B_103, C_104)=C_104 | ~m1_subset_1(C_104, u1_struct_0(k9_yellow_6(A_102, B_103))) | ~m1_subset_1(B_103, u1_struct_0(A_102)) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.18/3.45  tff(c_248, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_238])).
% 10.18/3.45  tff(c_256, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_248])).
% 10.18/3.45  tff(c_257, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_60, c_256])).
% 10.18/3.45  tff(c_341, plain, (![B_118, A_119, C_120]: (r2_hidden(B_118, '#skF_3'(A_119, B_118, C_120)) | ~m1_subset_1(C_120, u1_struct_0(k9_yellow_6(A_119, B_118))) | ~m1_subset_1(B_118, u1_struct_0(A_119)) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.18/3.45  tff(c_357, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_341])).
% 10.18/3.45  tff(c_368, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_257, c_357])).
% 10.18/3.45  tff(c_369, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_60, c_368])).
% 10.18/3.45  tff(c_50, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.18/3.45  tff(c_245, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_238])).
% 10.18/3.45  tff(c_252, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_245])).
% 10.18/3.45  tff(c_253, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_60, c_252])).
% 10.18/3.45  tff(c_355, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_7')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_341])).
% 10.18/3.45  tff(c_364, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_253, c_355])).
% 10.18/3.45  tff(c_365, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_60, c_364])).
% 10.18/3.45  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.18/3.45  tff(c_932, plain, (![A_169, B_170, C_171]: (m1_subset_1('#skF_3'(A_169, B_170, C_171), k1_zfmisc_1(u1_struct_0(A_169))) | ~m1_subset_1(C_171, u1_struct_0(k9_yellow_6(A_169, B_170))) | ~m1_subset_1(B_170, u1_struct_0(A_169)) | ~l1_pre_topc(A_169) | ~v2_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.18/3.45  tff(c_940, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_257, c_932])).
% 10.18/3.45  tff(c_947, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_940])).
% 10.18/3.45  tff(c_948, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_947])).
% 10.18/3.45  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.18/3.45  tff(c_958, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_948, c_26])).
% 10.18/3.45  tff(c_20, plain, (![A_7, C_9, B_8]: (r1_tarski(k3_xboole_0(A_7, C_9), B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.18/3.45  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.18/3.45  tff(c_281, plain, (![A_107, B_108, C_109]: (v3_pre_topc('#skF_3'(A_107, B_108, C_109), A_107) | ~m1_subset_1(C_109, u1_struct_0(k9_yellow_6(A_107, B_108))) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.18/3.45  tff(c_291, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_281])).
% 10.18/3.45  tff(c_300, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_257, c_291])).
% 10.18/3.45  tff(c_301, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_300])).
% 10.18/3.45  tff(c_289, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_281])).
% 10.18/3.45  tff(c_296, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_253, c_289])).
% 10.18/3.45  tff(c_297, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_296])).
% 10.18/3.45  tff(c_943, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_253, c_932])).
% 10.18/3.45  tff(c_950, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_50, c_943])).
% 10.18/3.45  tff(c_951, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_950])).
% 10.18/3.45  tff(c_1172, plain, (![B_187, C_188, A_189]: (v3_pre_topc(k3_xboole_0(B_187, C_188), A_189) | ~m1_subset_1(C_188, k1_zfmisc_1(u1_struct_0(A_189))) | ~v3_pre_topc(C_188, A_189) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_189))) | ~v3_pre_topc(B_187, A_189) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.18/3.45  tff(c_1174, plain, (![B_187]: (v3_pre_topc(k3_xboole_0(B_187, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_187, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_951, c_1172])).
% 10.18/3.45  tff(c_1238, plain, (![B_190]: (v3_pre_topc(k3_xboole_0(B_190, '#skF_7'), '#skF_4') | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_190, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_297, c_1174])).
% 10.18/3.45  tff(c_1244, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_948, c_1238])).
% 10.18/3.45  tff(c_1306, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_301, c_1244])).
% 10.18/3.45  tff(c_1417, plain, (![C_193, A_194, B_195]: (r2_hidden(C_193, u1_struct_0(k9_yellow_6(A_194, B_195))) | ~v3_pre_topc(C_193, A_194) | ~r2_hidden(B_195, C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~m1_subset_1(B_195, u1_struct_0(A_194)) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_109])).
% 10.18/3.45  tff(c_24, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.18/3.45  tff(c_9842, plain, (![C_573, A_574, B_575]: (m1_subset_1(C_573, u1_struct_0(k9_yellow_6(A_574, B_575))) | ~v3_pre_topc(C_573, A_574) | ~r2_hidden(B_575, C_573) | ~m1_subset_1(C_573, k1_zfmisc_1(u1_struct_0(A_574))) | ~m1_subset_1(B_575, u1_struct_0(A_574)) | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574) | v2_struct_0(A_574))), inference(resolution, [status(thm)], [c_1417, c_24])).
% 10.18/3.45  tff(c_48, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 10.18/3.45  tff(c_9852, plain, (~v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_9842, c_48])).
% 10.18/3.45  tff(c_9858, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1306, c_9852])).
% 10.18/3.45  tff(c_9859, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_9858])).
% 10.18/3.45  tff(c_9860, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_9859])).
% 10.18/3.45  tff(c_9864, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_9860])).
% 10.18/3.45  tff(c_9867, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_9864])).
% 10.18/3.45  tff(c_9871, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_958, c_9867])).
% 10.18/3.45  tff(c_9872, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_9859])).
% 10.18/3.45  tff(c_9876, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_9872])).
% 10.18/3.45  tff(c_9880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_369, c_365, c_9876])).
% 10.18/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.45  
% 10.18/3.45  Inference rules
% 10.18/3.45  ----------------------
% 10.18/3.45  #Ref     : 0
% 10.18/3.45  #Sup     : 2152
% 10.18/3.45  #Fact    : 0
% 10.18/3.45  #Define  : 0
% 10.18/3.45  #Split   : 1
% 10.18/3.45  #Chain   : 0
% 10.18/3.45  #Close   : 0
% 10.18/3.45  
% 10.18/3.45  Ordering : KBO
% 10.18/3.45  
% 10.18/3.45  Simplification rules
% 10.18/3.45  ----------------------
% 10.18/3.45  #Subsume      : 187
% 10.18/3.45  #Demod        : 391
% 10.18/3.45  #Tautology    : 123
% 10.18/3.45  #SimpNegUnit  : 15
% 10.18/3.45  #BackRed      : 0
% 10.18/3.45  
% 10.18/3.45  #Partial instantiations: 0
% 10.18/3.45  #Strategies tried      : 1
% 10.18/3.45  
% 10.18/3.45  Timing (in seconds)
% 10.18/3.45  ----------------------
% 10.18/3.46  Preprocessing        : 0.31
% 10.18/3.46  Parsing              : 0.16
% 10.18/3.46  CNF conversion       : 0.03
% 10.18/3.46  Main loop            : 2.35
% 10.18/3.46  Inferencing          : 0.67
% 10.18/3.46  Reduction            : 0.49
% 10.18/3.46  Demodulation         : 0.35
% 10.18/3.46  BG Simplification    : 0.09
% 10.18/3.46  Subsumption          : 0.91
% 10.18/3.46  Abstraction          : 0.17
% 10.18/3.46  MUC search           : 0.00
% 10.18/3.46  Cooper               : 0.00
% 10.18/3.46  Total                : 2.70
% 10.18/3.46  Index Insertion      : 0.00
% 10.18/3.46  Index Deletion       : 0.00
% 10.18/3.46  Index Matching       : 0.00
% 10.18/3.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

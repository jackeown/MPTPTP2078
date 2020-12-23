%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:13 EST 2020

% Result     : Theorem 8.11s
% Output     : CNFRefutation 8.25s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 302 expanded)
%              Number of leaves         :   31 ( 132 expanded)
%              Depth                    :   15
%              Number of atoms          :  199 (1154 expanded)
%              Number of equality atoms :   12 (  52 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k8_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * $i * $i ) > $i )).

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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k8_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_subset_1)).

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

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_280,plain,(
    ! [A_104,B_105,C_106] :
      ( '#skF_3'(A_104,B_105,C_106) = C_106
      | ~ m1_subset_1(C_106,u1_struct_0(k9_yellow_6(A_104,B_105)))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_298,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_280])).

tff(c_308,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_298])).

tff(c_309,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_308])).

tff(c_351,plain,(
    ! [B_110,A_111,C_112] :
      ( r2_hidden(B_110,'#skF_3'(A_111,B_110,C_112))
      | ~ m1_subset_1(C_112,u1_struct_0(k9_yellow_6(A_111,B_110)))
      | ~ m1_subset_1(B_110,u1_struct_0(A_111))
      | ~ l1_pre_topc(A_111)
      | ~ v2_pre_topc(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_367,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_351])).

tff(c_378,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_309,c_367])).

tff(c_379,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_378])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_295,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_280])).

tff(c_304,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_295])).

tff(c_305,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_304])).

tff(c_365,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_351])).

tff(c_374,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_305,c_365])).

tff(c_375,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_374])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_904,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1('#skF_3'(A_150,B_151,C_152),k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(C_152,u1_struct_0(k9_yellow_6(A_150,B_151)))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_911,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_904])).

tff(c_918,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_911])).

tff(c_919,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_918])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] :
      ( k8_subset_1(A_10,B_11,C_12) = k3_xboole_0(B_11,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_937,plain,(
    ! [C_155] : k8_subset_1(u1_struct_0('#skF_4'),'#skF_6',C_155) = k3_xboole_0('#skF_6',C_155) ),
    inference(resolution,[status(thm)],[c_919,c_22])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k8_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_946,plain,(
    ! [C_155] :
      ( m1_subset_1(k3_xboole_0('#skF_6',C_155),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_937,c_20])).

tff(c_954,plain,(
    ! [C_155] : m1_subset_1(k3_xboole_0('#skF_6',C_155),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_946])).

tff(c_719,plain,(
    ! [A_140,B_141,C_142] :
      ( v3_pre_topc('#skF_3'(A_140,B_141,C_142),A_140)
      | ~ m1_subset_1(C_142,u1_struct_0(k9_yellow_6(A_140,B_141)))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_753,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_719])).

tff(c_770,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_309,c_753])).

tff(c_771,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_770])).

tff(c_751,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_719])).

tff(c_766,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_305,c_751])).

tff(c_767,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_766])).

tff(c_914,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_904])).

tff(c_921,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_48,c_914])).

tff(c_922,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_921])).

tff(c_1241,plain,(
    ! [B_170,C_171,A_172] :
      ( v3_pre_topc(k3_xboole_0(B_170,C_171),A_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ v3_pre_topc(C_171,A_172)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ v3_pre_topc(B_170,A_172)
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1249,plain,(
    ! [B_170] :
      ( v3_pre_topc(k3_xboole_0(B_170,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_170,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_922,c_1241])).

tff(c_1412,plain,(
    ! [B_178] :
      ( v3_pre_topc(k3_xboole_0(B_178,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_178,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_767,c_1249])).

tff(c_1427,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_919,c_1412])).

tff(c_1484,plain,(
    v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_1427])).

tff(c_1607,plain,(
    ! [C_185,A_186,B_187] :
      ( r2_hidden(C_185,u1_struct_0(k9_yellow_6(A_186,B_187)))
      | ~ v3_pre_topc(C_185,A_186)
      | ~ r2_hidden(B_187,C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(u1_struct_0(A_186)))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_pre_topc(A_186)
      | ~ v2_pre_topc(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_26,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8048,plain,(
    ! [C_443,A_444,B_445] :
      ( m1_subset_1(C_443,u1_struct_0(k9_yellow_6(A_444,B_445)))
      | ~ v3_pre_topc(C_443,A_444)
      | ~ r2_hidden(B_445,C_443)
      | ~ m1_subset_1(C_443,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ m1_subset_1(B_445,u1_struct_0(A_444))
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(resolution,[status(thm)],[c_1607,c_26])).

tff(c_46,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_8058,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_8048,c_46])).

tff(c_8064,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_954,c_1484,c_8058])).

tff(c_8065,plain,(
    ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_8064])).

tff(c_8068,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_8065])).

tff(c_8072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_375,c_8068])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.11/2.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/2.85  
% 8.11/2.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/2.86  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k8_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 8.11/2.86  
% 8.11/2.86  %Foreground sorts:
% 8.11/2.86  
% 8.11/2.86  
% 8.11/2.86  %Background operators:
% 8.11/2.86  
% 8.11/2.86  
% 8.11/2.86  %Foreground operators:
% 8.11/2.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.11/2.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.11/2.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 8.11/2.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.11/2.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.11/2.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.11/2.86  tff('#skF_7', type, '#skF_7': $i).
% 8.11/2.86  tff(k8_subset_1, type, k8_subset_1: ($i * $i * $i) > $i).
% 8.11/2.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.11/2.86  tff('#skF_5', type, '#skF_5': $i).
% 8.11/2.86  tff('#skF_6', type, '#skF_6': $i).
% 8.11/2.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.11/2.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.11/2.86  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 8.11/2.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.11/2.86  tff('#skF_4', type, '#skF_4': $i).
% 8.11/2.86  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.11/2.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.11/2.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.11/2.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.11/2.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.11/2.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.11/2.86  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.11/2.86  
% 8.25/2.87  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_9)).
% 8.25/2.87  tff(f_90, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 8.25/2.87  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 8.25/2.87  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 8.25/2.87  tff(f_38, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k8_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_subset_1)).
% 8.25/2.87  tff(f_68, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 8.25/2.87  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 8.25/2.87  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.25/2.87  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.25/2.87  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.25/2.87  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.25/2.87  tff(c_52, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.25/2.87  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.25/2.87  tff(c_280, plain, (![A_104, B_105, C_106]: ('#skF_3'(A_104, B_105, C_106)=C_106 | ~m1_subset_1(C_106, u1_struct_0(k9_yellow_6(A_104, B_105))) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.25/2.87  tff(c_298, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_280])).
% 8.25/2.87  tff(c_308, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_298])).
% 8.25/2.87  tff(c_309, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_308])).
% 8.25/2.87  tff(c_351, plain, (![B_110, A_111, C_112]: (r2_hidden(B_110, '#skF_3'(A_111, B_110, C_112)) | ~m1_subset_1(C_112, u1_struct_0(k9_yellow_6(A_111, B_110))) | ~m1_subset_1(B_110, u1_struct_0(A_111)) | ~l1_pre_topc(A_111) | ~v2_pre_topc(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.25/2.87  tff(c_367, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_351])).
% 8.25/2.87  tff(c_378, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_309, c_367])).
% 8.25/2.87  tff(c_379, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_378])).
% 8.25/2.87  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.25/2.87  tff(c_295, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_280])).
% 8.25/2.87  tff(c_304, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_295])).
% 8.25/2.87  tff(c_305, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_58, c_304])).
% 8.25/2.87  tff(c_365, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_7')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_351])).
% 8.25/2.87  tff(c_374, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_305, c_365])).
% 8.25/2.87  tff(c_375, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_374])).
% 8.25/2.87  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.25/2.87  tff(c_904, plain, (![A_150, B_151, C_152]: (m1_subset_1('#skF_3'(A_150, B_151, C_152), k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(C_152, u1_struct_0(k9_yellow_6(A_150, B_151))) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.25/2.87  tff(c_911, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_309, c_904])).
% 8.25/2.87  tff(c_918, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_911])).
% 8.25/2.87  tff(c_919, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_918])).
% 8.25/2.87  tff(c_22, plain, (![A_10, B_11, C_12]: (k8_subset_1(A_10, B_11, C_12)=k3_xboole_0(B_11, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.25/2.87  tff(c_937, plain, (![C_155]: (k8_subset_1(u1_struct_0('#skF_4'), '#skF_6', C_155)=k3_xboole_0('#skF_6', C_155))), inference(resolution, [status(thm)], [c_919, c_22])).
% 8.25/2.87  tff(c_20, plain, (![A_7, B_8, C_9]: (m1_subset_1(k8_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.25/2.87  tff(c_946, plain, (![C_155]: (m1_subset_1(k3_xboole_0('#skF_6', C_155), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_937, c_20])).
% 8.25/2.87  tff(c_954, plain, (![C_155]: (m1_subset_1(k3_xboole_0('#skF_6', C_155), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_919, c_946])).
% 8.25/2.87  tff(c_719, plain, (![A_140, B_141, C_142]: (v3_pre_topc('#skF_3'(A_140, B_141, C_142), A_140) | ~m1_subset_1(C_142, u1_struct_0(k9_yellow_6(A_140, B_141))) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.25/2.87  tff(c_753, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_719])).
% 8.25/2.87  tff(c_770, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_309, c_753])).
% 8.25/2.87  tff(c_771, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_770])).
% 8.25/2.87  tff(c_751, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_719])).
% 8.25/2.87  tff(c_766, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_305, c_751])).
% 8.25/2.87  tff(c_767, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_766])).
% 8.25/2.87  tff(c_914, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_305, c_904])).
% 8.25/2.87  tff(c_921, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_48, c_914])).
% 8.25/2.87  tff(c_922, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_921])).
% 8.25/2.87  tff(c_1241, plain, (![B_170, C_171, A_172]: (v3_pre_topc(k3_xboole_0(B_170, C_171), A_172) | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~v3_pre_topc(C_171, A_172) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0(A_172))) | ~v3_pre_topc(B_170, A_172) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.25/2.87  tff(c_1249, plain, (![B_170]: (v3_pre_topc(k3_xboole_0(B_170, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_170, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_922, c_1241])).
% 8.25/2.87  tff(c_1412, plain, (![B_178]: (v3_pre_topc(k3_xboole_0(B_178, '#skF_7'), '#skF_4') | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_178, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_767, c_1249])).
% 8.25/2.87  tff(c_1427, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_919, c_1412])).
% 8.25/2.87  tff(c_1484, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_771, c_1427])).
% 8.25/2.87  tff(c_1607, plain, (![C_185, A_186, B_187]: (r2_hidden(C_185, u1_struct_0(k9_yellow_6(A_186, B_187))) | ~v3_pre_topc(C_185, A_186) | ~r2_hidden(B_187, C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(u1_struct_0(A_186))) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_pre_topc(A_186) | ~v2_pre_topc(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.25/2.87  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(A_15, B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.25/2.87  tff(c_8048, plain, (![C_443, A_444, B_445]: (m1_subset_1(C_443, u1_struct_0(k9_yellow_6(A_444, B_445))) | ~v3_pre_topc(C_443, A_444) | ~r2_hidden(B_445, C_443) | ~m1_subset_1(C_443, k1_zfmisc_1(u1_struct_0(A_444))) | ~m1_subset_1(B_445, u1_struct_0(A_444)) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(resolution, [status(thm)], [c_1607, c_26])).
% 8.25/2.87  tff(c_46, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.25/2.87  tff(c_8058, plain, (~v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_8048, c_46])).
% 8.25/2.87  tff(c_8064, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_954, c_1484, c_8058])).
% 8.25/2.87  tff(c_8065, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58, c_8064])).
% 8.25/2.87  tff(c_8068, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_8065])).
% 8.25/2.87  tff(c_8072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_379, c_375, c_8068])).
% 8.25/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.25/2.87  
% 8.25/2.87  Inference rules
% 8.25/2.87  ----------------------
% 8.25/2.87  #Ref     : 0
% 8.25/2.87  #Sup     : 1680
% 8.25/2.87  #Fact    : 0
% 8.25/2.87  #Define  : 0
% 8.25/2.87  #Split   : 0
% 8.25/2.87  #Chain   : 0
% 8.25/2.87  #Close   : 0
% 8.25/2.87  
% 8.25/2.87  Ordering : KBO
% 8.25/2.87  
% 8.25/2.87  Simplification rules
% 8.25/2.87  ----------------------
% 8.25/2.87  #Subsume      : 193
% 8.25/2.87  #Demod        : 435
% 8.25/2.87  #Tautology    : 109
% 8.25/2.87  #SimpNegUnit  : 13
% 8.25/2.87  #BackRed      : 0
% 8.25/2.87  
% 8.25/2.87  #Partial instantiations: 0
% 8.25/2.87  #Strategies tried      : 1
% 8.25/2.87  
% 8.25/2.87  Timing (in seconds)
% 8.25/2.87  ----------------------
% 8.25/2.88  Preprocessing        : 0.34
% 8.25/2.88  Parsing              : 0.17
% 8.25/2.88  CNF conversion       : 0.03
% 8.25/2.88  Main loop            : 1.77
% 8.25/2.88  Inferencing          : 0.57
% 8.25/2.88  Reduction            : 0.44
% 8.25/2.88  Demodulation         : 0.33
% 8.25/2.88  BG Simplification    : 0.08
% 8.25/2.88  Subsumption          : 0.54
% 8.25/2.88  Abstraction          : 0.13
% 8.25/2.88  MUC search           : 0.00
% 8.25/2.88  Cooper               : 0.00
% 8.25/2.88  Total                : 2.14
% 8.25/2.88  Index Insertion      : 0.00
% 8.25/2.88  Index Deletion       : 0.00
% 8.25/2.88  Index Matching       : 0.00
% 8.25/2.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------

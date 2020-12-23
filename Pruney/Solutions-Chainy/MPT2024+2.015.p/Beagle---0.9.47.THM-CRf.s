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
% DateTime   : Thu Dec  3 10:31:16 EST 2020

% Result     : Theorem 17.18s
% Output     : CNFRefutation 17.18s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 728 expanded)
%              Number of leaves         :   29 ( 296 expanded)
%              Depth                    :   17
%              Number of atoms          :  210 (2932 expanded)
%              Number of equality atoms :   13 ( 139 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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
                   => m1_subset_1(k2_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

tff(f_92,axiom,(
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
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k2_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

tff(f_111,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_52,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_117,plain,(
    ! [A_88,B_89,C_90] :
      ( '#skF_3'(A_88,B_89,C_90) = C_90
      | ~ m1_subset_1(C_90,u1_struct_0(k9_yellow_6(A_88,B_89)))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_120,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_126,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_120])).

tff(c_127,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_126])).

tff(c_439,plain,(
    ! [B_111,A_112,C_113] :
      ( r2_hidden(B_111,'#skF_3'(A_112,B_111,C_113))
      | ~ m1_subset_1(C_113,u1_struct_0(k9_yellow_6(A_112,B_111)))
      | ~ m1_subset_1(B_111,u1_struct_0(A_112))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112)
      | v2_struct_0(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_441,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_439])).

tff(c_446,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_127,c_441])).

tff(c_447,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_446])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_123,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_130,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_123])).

tff(c_131,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_130])).

tff(c_1178,plain,(
    ! [A_150,B_151,C_152] :
      ( m1_subset_1('#skF_3'(A_150,B_151,C_152),k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(C_152,u1_struct_0(k9_yellow_6(A_150,B_151)))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1185,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_1178])).

tff(c_1192,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_1185])).

tff(c_1193,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1192])).

tff(c_1188,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_1178])).

tff(c_1195,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_46,c_1188])).

tff(c_1196,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1195])).

tff(c_22,plain,(
    ! [A_10,B_11,C_12] :
      ( k4_subset_1(A_10,B_11,C_12) = k2_xboole_0(B_11,C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_10))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1600,plain,(
    ! [B_166] :
      ( k4_subset_1(u1_struct_0('#skF_4'),B_166,'#skF_7') = k2_xboole_0(B_166,'#skF_7')
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_1196,c_22])).

tff(c_1645,plain,(
    k4_subset_1(u1_struct_0('#skF_4'),'#skF_6','#skF_7') = k2_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1193,c_1600])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k4_subset_1(A_7,B_8,C_9),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1714,plain,
    ( m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1645,c_20])).

tff(c_1720,plain,(
    m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1193,c_1196,c_1714])).

tff(c_378,plain,(
    ! [A_106,B_107,C_108] :
      ( v3_pre_topc('#skF_3'(A_106,B_107,C_108),A_106)
      | ~ m1_subset_1(C_108,u1_struct_0(k9_yellow_6(A_106,B_107)))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_382,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_378])).

tff(c_389,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_131,c_382])).

tff(c_390,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_389])).

tff(c_1259,plain,(
    ! [B_156,C_157,A_158] :
      ( v3_pre_topc(k2_xboole_0(B_156,C_157),A_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ v3_pre_topc(C_157,A_158)
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ v3_pre_topc(B_156,A_158)
      | ~ l1_pre_topc(A_158)
      | ~ v2_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1263,plain,(
    ! [B_156] :
      ( v3_pre_topc(k2_xboole_0(B_156,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_156,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1193,c_1259])).

tff(c_2483,plain,(
    ! [B_185] :
      ( v3_pre_topc(k2_xboole_0(B_185,'#skF_6'),'#skF_4')
      | ~ m1_subset_1(B_185,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_185,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_390,c_1263])).

tff(c_2544,plain,
    ( v3_pre_topc(k2_xboole_0(k2_xboole_0('#skF_6','#skF_7'),'#skF_6'),'#skF_4')
    | ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1720,c_2483])).

tff(c_2563,plain,(
    ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2544])).

tff(c_380,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_378])).

tff(c_385,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_127,c_380])).

tff(c_386,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_385])).

tff(c_1261,plain,(
    ! [B_156] :
      ( v3_pre_topc(k2_xboole_0(B_156,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_156,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1196,c_1259])).

tff(c_2577,plain,(
    ! [B_188] :
      ( v3_pre_topc(k2_xboole_0(B_188,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_188,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_188,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_386,c_1261])).

tff(c_2605,plain,
    ( v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1193,c_2577])).

tff(c_2650,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_2605])).

tff(c_2652,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2563,c_2650])).

tff(c_2654,plain,(
    v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2544])).

tff(c_1569,plain,(
    ! [C_163,A_164,B_165] :
      ( r2_hidden(C_163,u1_struct_0(k9_yellow_6(A_164,B_165)))
      | ~ v3_pre_topc(C_163,A_164)
      | ~ r2_hidden(B_165,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36133,plain,(
    ! [C_707,A_708,B_709] :
      ( m1_subset_1(C_707,u1_struct_0(k9_yellow_6(A_708,B_709)))
      | ~ v3_pre_topc(C_707,A_708)
      | ~ r2_hidden(B_709,C_707)
      | ~ m1_subset_1(C_707,k1_zfmisc_1(u1_struct_0(A_708)))
      | ~ m1_subset_1(B_709,u1_struct_0(A_708))
      | ~ l1_pre_topc(A_708)
      | ~ v2_pre_topc(A_708)
      | v2_struct_0(A_708) ) ),
    inference(resolution,[status(thm)],[c_1569,c_24])).

tff(c_44,plain,(
    ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36151,plain,
    ( ~ v3_pre_topc(k2_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k2_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36133,c_44])).

tff(c_36165,plain,
    ( ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_1720,c_2654,c_36151])).

tff(c_36166,plain,(
    ~ r2_hidden('#skF_5',k2_xboole_0('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_36165])).

tff(c_36169,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_36166])).

tff(c_36176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_36169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.18/8.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.18/8.81  
% 17.18/8.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.18/8.81  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k4_subset_1 > k9_yellow_6 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 17.18/8.81  
% 17.18/8.81  %Foreground sorts:
% 17.18/8.81  
% 17.18/8.81  
% 17.18/8.81  %Background operators:
% 17.18/8.81  
% 17.18/8.81  
% 17.18/8.81  %Foreground operators:
% 17.18/8.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 17.18/8.81  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.18/8.81  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 17.18/8.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.18/8.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.18/8.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 17.18/8.81  tff('#skF_7', type, '#skF_7': $i).
% 17.18/8.81  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 17.18/8.81  tff('#skF_5', type, '#skF_5': $i).
% 17.18/8.81  tff('#skF_6', type, '#skF_6': $i).
% 17.18/8.81  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.18/8.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.18/8.81  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 17.18/8.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.18/8.81  tff('#skF_4', type, '#skF_4': $i).
% 17.18/8.81  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.18/8.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.18/8.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 17.18/8.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.18/8.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 17.18/8.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.18/8.81  
% 17.18/8.82  tff(f_130, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k2_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_waybel_9)).
% 17.18/8.82  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 17.18/8.82  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 17.18/8.82  tff(f_46, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 17.18/8.82  tff(f_40, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 17.18/8.82  tff(f_70, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k2_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_tops_1)).
% 17.18/8.82  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 17.18/8.82  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 17.18/8.82  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 17.18/8.82  tff(c_54, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 17.18/8.82  tff(c_52, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 17.18/8.82  tff(c_50, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 17.18/8.82  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 17.18/8.82  tff(c_117, plain, (![A_88, B_89, C_90]: ('#skF_3'(A_88, B_89, C_90)=C_90 | ~m1_subset_1(C_90, u1_struct_0(k9_yellow_6(A_88, B_89))) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.18/8.82  tff(c_120, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_117])).
% 17.18/8.82  tff(c_126, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_120])).
% 17.18/8.82  tff(c_127, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_56, c_126])).
% 17.18/8.82  tff(c_439, plain, (![B_111, A_112, C_113]: (r2_hidden(B_111, '#skF_3'(A_112, B_111, C_113)) | ~m1_subset_1(C_113, u1_struct_0(k9_yellow_6(A_112, B_111))) | ~m1_subset_1(B_111, u1_struct_0(A_112)) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112) | v2_struct_0(A_112))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.18/8.82  tff(c_441, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_7')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_439])).
% 17.18/8.82  tff(c_446, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_127, c_441])).
% 17.18/8.82  tff(c_447, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_446])).
% 17.18/8.82  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.18/8.82  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 17.18/8.82  tff(c_123, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_117])).
% 17.18/8.82  tff(c_130, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_123])).
% 17.18/8.82  tff(c_131, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_56, c_130])).
% 17.18/8.82  tff(c_1178, plain, (![A_150, B_151, C_152]: (m1_subset_1('#skF_3'(A_150, B_151, C_152), k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(C_152, u1_struct_0(k9_yellow_6(A_150, B_151))) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.18/8.82  tff(c_1185, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_131, c_1178])).
% 17.18/8.82  tff(c_1192, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_48, c_1185])).
% 17.18/8.82  tff(c_1193, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1192])).
% 17.18/8.82  tff(c_1188, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_127, c_1178])).
% 17.18/8.82  tff(c_1195, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_46, c_1188])).
% 17.18/8.82  tff(c_1196, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1195])).
% 17.18/8.82  tff(c_22, plain, (![A_10, B_11, C_12]: (k4_subset_1(A_10, B_11, C_12)=k2_xboole_0(B_11, C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(A_10)) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 17.18/8.82  tff(c_1600, plain, (![B_166]: (k4_subset_1(u1_struct_0('#skF_4'), B_166, '#skF_7')=k2_xboole_0(B_166, '#skF_7') | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_1196, c_22])).
% 17.18/8.82  tff(c_1645, plain, (k4_subset_1(u1_struct_0('#skF_4'), '#skF_6', '#skF_7')=k2_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_1193, c_1600])).
% 17.18/8.82  tff(c_20, plain, (![A_7, B_8, C_9]: (m1_subset_1(k4_subset_1(A_7, B_8, C_9), k1_zfmisc_1(A_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 17.18/8.82  tff(c_1714, plain, (m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1645, c_20])).
% 17.18/8.82  tff(c_1720, plain, (m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1193, c_1196, c_1714])).
% 17.18/8.82  tff(c_378, plain, (![A_106, B_107, C_108]: (v3_pre_topc('#skF_3'(A_106, B_107, C_108), A_106) | ~m1_subset_1(C_108, u1_struct_0(k9_yellow_6(A_106, B_107))) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_92])).
% 17.18/8.82  tff(c_382, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_378])).
% 17.18/8.82  tff(c_389, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_131, c_382])).
% 17.18/8.82  tff(c_390, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_389])).
% 17.18/8.82  tff(c_1259, plain, (![B_156, C_157, A_158]: (v3_pre_topc(k2_xboole_0(B_156, C_157), A_158) | ~m1_subset_1(C_157, k1_zfmisc_1(u1_struct_0(A_158))) | ~v3_pre_topc(C_157, A_158) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_158))) | ~v3_pre_topc(B_156, A_158) | ~l1_pre_topc(A_158) | ~v2_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_70])).
% 17.18/8.82  tff(c_1263, plain, (![B_156]: (v3_pre_topc(k2_xboole_0(B_156, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_156, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1193, c_1259])).
% 17.18/8.82  tff(c_2483, plain, (![B_185]: (v3_pre_topc(k2_xboole_0(B_185, '#skF_6'), '#skF_4') | ~m1_subset_1(B_185, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_185, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_390, c_1263])).
% 17.18/8.82  tff(c_2544, plain, (v3_pre_topc(k2_xboole_0(k2_xboole_0('#skF_6', '#skF_7'), '#skF_6'), '#skF_4') | ~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_1720, c_2483])).
% 17.18/8.82  tff(c_2563, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2544])).
% 17.18/8.82  tff(c_380, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_46, c_378])).
% 17.18/8.82  tff(c_385, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_127, c_380])).
% 17.18/8.82  tff(c_386, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_385])).
% 17.18/8.82  tff(c_1261, plain, (![B_156]: (v3_pre_topc(k2_xboole_0(B_156, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_156, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1196, c_1259])).
% 17.18/8.82  tff(c_2577, plain, (![B_188]: (v3_pre_topc(k2_xboole_0(B_188, '#skF_7'), '#skF_4') | ~m1_subset_1(B_188, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_188, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_386, c_1261])).
% 17.18/8.82  tff(c_2605, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1193, c_2577])).
% 17.18/8.82  tff(c_2650, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_2605])).
% 17.18/8.82  tff(c_2652, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2563, c_2650])).
% 17.18/8.82  tff(c_2654, plain, (v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_2544])).
% 17.18/8.82  tff(c_1569, plain, (![C_163, A_164, B_165]: (r2_hidden(C_163, u1_struct_0(k9_yellow_6(A_164, B_165))) | ~v3_pre_topc(C_163, A_164) | ~r2_hidden(B_165, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(u1_struct_0(A_164))) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_111])).
% 17.18/8.82  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 17.18/8.82  tff(c_36133, plain, (![C_707, A_708, B_709]: (m1_subset_1(C_707, u1_struct_0(k9_yellow_6(A_708, B_709))) | ~v3_pre_topc(C_707, A_708) | ~r2_hidden(B_709, C_707) | ~m1_subset_1(C_707, k1_zfmisc_1(u1_struct_0(A_708))) | ~m1_subset_1(B_709, u1_struct_0(A_708)) | ~l1_pre_topc(A_708) | ~v2_pre_topc(A_708) | v2_struct_0(A_708))), inference(resolution, [status(thm)], [c_1569, c_24])).
% 17.18/8.82  tff(c_44, plain, (~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 17.18/8.82  tff(c_36151, plain, (~v3_pre_topc(k2_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k2_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36133, c_44])).
% 17.18/8.82  tff(c_36165, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_1720, c_2654, c_36151])).
% 17.18/8.82  tff(c_36166, plain, (~r2_hidden('#skF_5', k2_xboole_0('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_56, c_36165])).
% 17.18/8.82  tff(c_36169, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_4, c_36166])).
% 17.18/8.82  tff(c_36176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_447, c_36169])).
% 17.18/8.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.18/8.82  
% 17.18/8.82  Inference rules
% 17.18/8.82  ----------------------
% 17.18/8.82  #Ref     : 0
% 17.18/8.82  #Sup     : 7178
% 17.18/8.82  #Fact    : 26
% 17.18/8.82  #Define  : 0
% 17.18/8.82  #Split   : 12
% 17.18/8.82  #Chain   : 0
% 17.18/8.82  #Close   : 0
% 17.18/8.82  
% 17.18/8.82  Ordering : KBO
% 17.18/8.82  
% 17.18/8.82  Simplification rules
% 17.18/8.82  ----------------------
% 17.18/8.82  #Subsume      : 1028
% 17.18/8.82  #Demod        : 3282
% 17.18/8.82  #Tautology    : 1134
% 17.18/8.82  #SimpNegUnit  : 22
% 17.18/8.82  #BackRed      : 598
% 17.18/8.82  
% 17.18/8.82  #Partial instantiations: 0
% 17.18/8.82  #Strategies tried      : 1
% 17.18/8.82  
% 17.18/8.82  Timing (in seconds)
% 17.18/8.82  ----------------------
% 17.18/8.83  Preprocessing        : 0.33
% 17.18/8.83  Parsing              : 0.17
% 17.18/8.83  CNF conversion       : 0.03
% 17.18/8.83  Main loop            : 7.71
% 17.18/8.83  Inferencing          : 1.59
% 17.18/8.83  Reduction            : 2.35
% 17.18/8.83  Demodulation         : 1.89
% 17.18/8.83  BG Simplification    : 0.26
% 17.18/8.83  Subsumption          : 2.98
% 17.18/8.83  Abstraction          : 0.50
% 17.18/8.83  MUC search           : 0.00
% 17.18/8.83  Cooper               : 0.00
% 17.18/8.83  Total                : 8.07
% 17.18/8.83  Index Insertion      : 0.00
% 17.18/8.83  Index Deletion       : 0.00
% 17.18/8.83  Index Matching       : 0.00
% 17.18/8.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:36 EST 2020

% Result     : Theorem 5.18s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 236 expanded)
%              Number of leaves         :   33 (  88 expanded)
%              Depth                    :   14
%              Number of atoms          :  211 ( 854 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( m1_pre_topc(B,C)
                     => ( ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) )
                        | ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_52,axiom,(
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

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(c_62,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_50,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1234,plain,(
    ! [B_179,A_180] :
      ( l1_pre_topc(B_179)
      | ~ m1_pre_topc(B_179,A_180)
      | ~ l1_pre_topc(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1237,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1234])).

tff(c_1249,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1237])).

tff(c_32,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1240,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1234])).

tff(c_1252,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1240])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1166,plain,(
    ! [B_154,A_155] :
      ( l1_pre_topc(B_154)
      | ~ m1_pre_topc(B_154,A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1178,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1166])).

tff(c_1188,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1178])).

tff(c_1169,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1166])).

tff(c_1181,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1169])).

tff(c_71,plain,(
    ! [B_42,A_43] :
      ( l1_pre_topc(B_42)
      | ~ m1_pre_topc(B_42,A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_71])).

tff(c_89,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_77])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_74,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_86,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_74])).

tff(c_83,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_71])).

tff(c_93,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_83])).

tff(c_44,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_69,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_106,plain,(
    ! [B_61,A_62] :
      ( r1_tsep_1(B_61,A_62)
      | ~ r1_tsep_1(A_62,B_61)
      | ~ l1_struct_0(B_61)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_109,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_69,c_106])).

tff(c_110,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_113,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_110])).

tff(c_117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_113])).

tff(c_118,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_120,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_123,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_120])).

tff(c_127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_123])).

tff(c_129,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_119,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_154,plain,(
    ! [B_66,A_67] :
      ( m1_subset_1(u1_struct_0(B_66),k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_159,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(u1_struct_0(B_68),u1_struct_0(A_69))
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_154,c_28])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_173,plain,(
    ! [B_74,A_75] :
      ( k2_xboole_0(u1_struct_0(B_74),u1_struct_0(A_75)) = u1_struct_0(A_75)
      | ~ m1_pre_topc(B_74,A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_159,c_26])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_191,plain,(
    ! [D_76,B_77,A_78] :
      ( ~ r2_hidden(D_76,u1_struct_0(B_77))
      | r2_hidden(D_76,u1_struct_0(A_78))
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_6])).

tff(c_198,plain,(
    ! [B_77,B_8,A_78] :
      ( r2_hidden('#skF_3'(u1_struct_0(B_77),B_8),u1_struct_0(A_78))
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78)
      | r1_xboole_0(u1_struct_0(B_77),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_191])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    ! [A_72,B_73] :
      ( r1_xboole_0(u1_struct_0(A_72),u1_struct_0(B_73))
      | ~ r1_tsep_1(A_72,B_73)
      | ~ l1_struct_0(B_73)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_200,plain,(
    ! [C_79,B_80,A_81] :
      ( ~ r2_hidden(C_79,u1_struct_0(B_80))
      | ~ r2_hidden(C_79,u1_struct_0(A_81))
      | ~ r1_tsep_1(A_81,B_80)
      | ~ l1_struct_0(B_80)
      | ~ l1_struct_0(A_81) ) ),
    inference(resolution,[status(thm)],[c_165,c_20])).

tff(c_918,plain,(
    ! [A_133,B_134,A_135] :
      ( ~ r2_hidden('#skF_3'(A_133,u1_struct_0(B_134)),u1_struct_0(A_135))
      | ~ r1_tsep_1(A_135,B_134)
      | ~ l1_struct_0(B_134)
      | ~ l1_struct_0(A_135)
      | r1_xboole_0(A_133,u1_struct_0(B_134)) ) ),
    inference(resolution,[status(thm)],[c_22,c_200])).

tff(c_1019,plain,(
    ! [A_144,B_145,B_146] :
      ( ~ r1_tsep_1(A_144,B_145)
      | ~ l1_struct_0(B_145)
      | ~ l1_struct_0(A_144)
      | ~ m1_pre_topc(B_146,A_144)
      | ~ l1_pre_topc(A_144)
      | r1_xboole_0(u1_struct_0(B_146),u1_struct_0(B_145)) ) ),
    inference(resolution,[status(thm)],[c_198,c_918])).

tff(c_1023,plain,(
    ! [B_146] :
      ( ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0('#skF_6')
      | ~ m1_pre_topc(B_146,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | r1_xboole_0(u1_struct_0(B_146),u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_69,c_1019])).

tff(c_1040,plain,(
    ! [B_148] :
      ( ~ m1_pre_topc(B_148,'#skF_6')
      | r1_xboole_0(u1_struct_0(B_148),u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_119,c_129,c_1023])).

tff(c_36,plain,(
    ! [A_20,B_22] :
      ( r1_tsep_1(A_20,B_22)
      | ~ r1_xboole_0(u1_struct_0(A_20),u1_struct_0(B_22))
      | ~ l1_struct_0(B_22)
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1043,plain,(
    ! [B_148] :
      ( r1_tsep_1(B_148,'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(B_148)
      | ~ m1_pre_topc(B_148,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1040,c_36])).

tff(c_1072,plain,(
    ! [B_150] :
      ( r1_tsep_1(B_150,'#skF_7')
      | ~ l1_struct_0(B_150)
      | ~ m1_pre_topc(B_150,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_1043])).

tff(c_46,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_68,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1084,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1072,c_68])).

tff(c_1099,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1084])).

tff(c_1159,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_1099])).

tff(c_1163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1159])).

tff(c_1165,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1164,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1203,plain,(
    ! [B_175,A_176] :
      ( r1_tsep_1(B_175,A_176)
      | ~ r1_tsep_1(A_176,B_175)
      | ~ l1_struct_0(B_175)
      | ~ l1_struct_0(A_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1205,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1164,c_1203])).

tff(c_1208,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1165,c_1205])).

tff(c_1209,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1208])).

tff(c_1212,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1209])).

tff(c_1216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_1212])).

tff(c_1217,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1208])).

tff(c_1226,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_1217])).

tff(c_1230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1188,c_1226])).

tff(c_1231,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1232,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1271,plain,(
    ! [B_200,A_201] :
      ( r1_tsep_1(B_200,A_201)
      | ~ r1_tsep_1(A_201,B_200)
      | ~ l1_struct_0(B_200)
      | ~ l1_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1275,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1232,c_1271])).

tff(c_1279,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1231,c_1275])).

tff(c_1280,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1279])).

tff(c_1283,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_1280])).

tff(c_1287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_1283])).

tff(c_1288,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1279])).

tff(c_1292,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1288])).

tff(c_1296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:33:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.18/2.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.41/2.92  
% 5.41/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.46/2.92  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.46/2.92  
% 5.46/2.92  %Foreground sorts:
% 5.46/2.92  
% 5.46/2.92  
% 5.46/2.92  %Background operators:
% 5.46/2.92  
% 5.46/2.92  
% 5.46/2.92  %Foreground operators:
% 5.46/2.92  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.46/2.92  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.46/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.46/2.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.46/2.92  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.46/2.92  tff('#skF_7', type, '#skF_7': $i).
% 5.46/2.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.46/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.46/2.92  tff('#skF_5', type, '#skF_5': $i).
% 5.46/2.92  tff('#skF_6', type, '#skF_6': $i).
% 5.46/2.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.46/2.92  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.46/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.46/2.92  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.46/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.46/2.92  tff('#skF_4', type, '#skF_4': $i).
% 5.46/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.46/2.92  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.46/2.92  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.46/2.92  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 5.46/2.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.46/2.92  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.46/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.46/2.92  
% 5.46/2.98  tff(f_133, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 5.46/2.98  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.46/2.98  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.46/2.98  tff(f_88, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 5.46/2.98  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 5.46/2.98  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.46/2.98  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.46/2.98  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.46/2.98  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.46/2.98  tff(f_80, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 5.46/2.98  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.46/2.98  tff(c_50, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.46/2.98  tff(c_1234, plain, (![B_179, A_180]: (l1_pre_topc(B_179) | ~m1_pre_topc(B_179, A_180) | ~l1_pre_topc(A_180))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.46/2.98  tff(c_1237, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1234])).
% 5.46/2.98  tff(c_1249, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1237])).
% 5.46/2.98  tff(c_32, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.46/2.98  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.46/2.98  tff(c_1240, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1234])).
% 5.46/2.98  tff(c_1252, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1240])).
% 5.46/2.98  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.46/2.98  tff(c_1166, plain, (![B_154, A_155]: (l1_pre_topc(B_154) | ~m1_pre_topc(B_154, A_155) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.46/2.98  tff(c_1178, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1166])).
% 5.46/2.98  tff(c_1188, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1178])).
% 5.46/2.98  tff(c_1169, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1166])).
% 5.46/2.98  tff(c_1181, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1169])).
% 5.46/2.98  tff(c_71, plain, (![B_42, A_43]: (l1_pre_topc(B_42) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.46/2.98  tff(c_77, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_71])).
% 5.46/2.98  tff(c_89, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_77])).
% 5.46/2.98  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.46/2.98  tff(c_74, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_71])).
% 5.46/2.98  tff(c_86, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_74])).
% 5.46/2.98  tff(c_83, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_71])).
% 5.46/2.98  tff(c_93, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_83])).
% 5.46/2.98  tff(c_44, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.46/2.98  tff(c_69, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 5.46/2.98  tff(c_106, plain, (![B_61, A_62]: (r1_tsep_1(B_61, A_62) | ~r1_tsep_1(A_62, B_61) | ~l1_struct_0(B_61) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.46/2.98  tff(c_109, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_69, c_106])).
% 5.46/2.98  tff(c_110, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_109])).
% 5.46/2.98  tff(c_113, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_32, c_110])).
% 5.46/2.98  tff(c_117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_113])).
% 5.46/2.98  tff(c_118, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_109])).
% 5.46/2.98  tff(c_120, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_118])).
% 5.46/2.98  tff(c_123, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_120])).
% 5.46/2.98  tff(c_127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_123])).
% 5.46/2.98  tff(c_129, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_118])).
% 5.46/2.98  tff(c_119, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_109])).
% 5.46/2.98  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.46/2.98  tff(c_154, plain, (![B_66, A_67]: (m1_subset_1(u1_struct_0(B_66), k1_zfmisc_1(u1_struct_0(A_67))) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.46/2.98  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.46/2.98  tff(c_159, plain, (![B_68, A_69]: (r1_tarski(u1_struct_0(B_68), u1_struct_0(A_69)) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_154, c_28])).
% 5.46/2.98  tff(c_26, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.46/2.98  tff(c_173, plain, (![B_74, A_75]: (k2_xboole_0(u1_struct_0(B_74), u1_struct_0(A_75))=u1_struct_0(A_75) | ~m1_pre_topc(B_74, A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_159, c_26])).
% 5.46/2.98  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.46/2.98  tff(c_191, plain, (![D_76, B_77, A_78]: (~r2_hidden(D_76, u1_struct_0(B_77)) | r2_hidden(D_76, u1_struct_0(A_78)) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78))), inference(superposition, [status(thm), theory('equality')], [c_173, c_6])).
% 5.46/2.98  tff(c_198, plain, (![B_77, B_8, A_78]: (r2_hidden('#skF_3'(u1_struct_0(B_77), B_8), u1_struct_0(A_78)) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78) | r1_xboole_0(u1_struct_0(B_77), B_8))), inference(resolution, [status(thm)], [c_24, c_191])).
% 5.46/2.98  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.46/2.98  tff(c_165, plain, (![A_72, B_73]: (r1_xboole_0(u1_struct_0(A_72), u1_struct_0(B_73)) | ~r1_tsep_1(A_72, B_73) | ~l1_struct_0(B_73) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.46/2.98  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.46/2.98  tff(c_200, plain, (![C_79, B_80, A_81]: (~r2_hidden(C_79, u1_struct_0(B_80)) | ~r2_hidden(C_79, u1_struct_0(A_81)) | ~r1_tsep_1(A_81, B_80) | ~l1_struct_0(B_80) | ~l1_struct_0(A_81))), inference(resolution, [status(thm)], [c_165, c_20])).
% 5.46/2.98  tff(c_918, plain, (![A_133, B_134, A_135]: (~r2_hidden('#skF_3'(A_133, u1_struct_0(B_134)), u1_struct_0(A_135)) | ~r1_tsep_1(A_135, B_134) | ~l1_struct_0(B_134) | ~l1_struct_0(A_135) | r1_xboole_0(A_133, u1_struct_0(B_134)))), inference(resolution, [status(thm)], [c_22, c_200])).
% 5.46/2.98  tff(c_1019, plain, (![A_144, B_145, B_146]: (~r1_tsep_1(A_144, B_145) | ~l1_struct_0(B_145) | ~l1_struct_0(A_144) | ~m1_pre_topc(B_146, A_144) | ~l1_pre_topc(A_144) | r1_xboole_0(u1_struct_0(B_146), u1_struct_0(B_145)))), inference(resolution, [status(thm)], [c_198, c_918])).
% 5.46/2.98  tff(c_1023, plain, (![B_146]: (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | ~m1_pre_topc(B_146, '#skF_6') | ~l1_pre_topc('#skF_6') | r1_xboole_0(u1_struct_0(B_146), u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_69, c_1019])).
% 5.46/2.98  tff(c_1040, plain, (![B_148]: (~m1_pre_topc(B_148, '#skF_6') | r1_xboole_0(u1_struct_0(B_148), u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_119, c_129, c_1023])).
% 5.46/2.98  tff(c_36, plain, (![A_20, B_22]: (r1_tsep_1(A_20, B_22) | ~r1_xboole_0(u1_struct_0(A_20), u1_struct_0(B_22)) | ~l1_struct_0(B_22) | ~l1_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.46/2.98  tff(c_1043, plain, (![B_148]: (r1_tsep_1(B_148, '#skF_7') | ~l1_struct_0('#skF_7') | ~l1_struct_0(B_148) | ~m1_pre_topc(B_148, '#skF_6'))), inference(resolution, [status(thm)], [c_1040, c_36])).
% 5.46/2.98  tff(c_1072, plain, (![B_150]: (r1_tsep_1(B_150, '#skF_7') | ~l1_struct_0(B_150) | ~m1_pre_topc(B_150, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_1043])).
% 5.46/2.98  tff(c_46, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.46/2.98  tff(c_68, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_46])).
% 5.46/2.98  tff(c_1084, plain, (~l1_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1072, c_68])).
% 5.46/2.98  tff(c_1099, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1084])).
% 5.46/2.98  tff(c_1159, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_32, c_1099])).
% 5.46/2.98  tff(c_1163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_1159])).
% 5.46/2.98  tff(c_1165, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 5.46/2.98  tff(c_1164, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 5.46/2.98  tff(c_1203, plain, (![B_175, A_176]: (r1_tsep_1(B_175, A_176) | ~r1_tsep_1(A_176, B_175) | ~l1_struct_0(B_175) | ~l1_struct_0(A_176))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.46/2.98  tff(c_1205, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1164, c_1203])).
% 5.46/2.98  tff(c_1208, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1165, c_1205])).
% 5.46/2.98  tff(c_1209, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1208])).
% 5.46/2.98  tff(c_1212, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1209])).
% 5.46/2.98  tff(c_1216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1181, c_1212])).
% 5.46/2.98  tff(c_1217, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1208])).
% 5.46/2.98  tff(c_1226, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_32, c_1217])).
% 5.46/2.98  tff(c_1230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1188, c_1226])).
% 5.46/2.98  tff(c_1231, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 5.46/2.98  tff(c_1232, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 5.46/2.98  tff(c_1271, plain, (![B_200, A_201]: (r1_tsep_1(B_200, A_201) | ~r1_tsep_1(A_201, B_200) | ~l1_struct_0(B_200) | ~l1_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.46/2.98  tff(c_1275, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1232, c_1271])).
% 5.46/2.98  tff(c_1279, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1231, c_1275])).
% 5.46/2.98  tff(c_1280, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1279])).
% 5.46/2.98  tff(c_1283, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_32, c_1280])).
% 5.46/2.98  tff(c_1287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1252, c_1283])).
% 5.46/2.98  tff(c_1288, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_1279])).
% 5.46/2.98  tff(c_1292, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1288])).
% 5.46/2.98  tff(c_1296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1292])).
% 5.46/2.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.46/2.98  
% 5.46/2.98  Inference rules
% 5.46/2.98  ----------------------
% 5.46/2.98  #Ref     : 0
% 5.46/2.98  #Sup     : 230
% 5.46/2.98  #Fact    : 10
% 5.46/2.98  #Define  : 0
% 5.46/2.98  #Split   : 9
% 5.46/2.98  #Chain   : 0
% 5.46/2.98  #Close   : 0
% 5.46/2.98  
% 5.46/2.98  Ordering : KBO
% 5.46/2.98  
% 5.46/2.98  Simplification rules
% 5.46/2.98  ----------------------
% 5.46/2.98  #Subsume      : 35
% 5.46/2.98  #Demod        : 88
% 5.46/2.98  #Tautology    : 46
% 5.46/2.98  #SimpNegUnit  : 2
% 5.46/2.98  #BackRed      : 2
% 5.46/2.98  
% 5.46/2.98  #Partial instantiations: 0
% 5.46/2.98  #Strategies tried      : 1
% 5.46/2.98  
% 5.46/2.98  Timing (in seconds)
% 5.46/2.98  ----------------------
% 5.46/2.98  Preprocessing        : 0.58
% 5.46/3.00  Parsing              : 0.33
% 5.46/3.00  CNF conversion       : 0.04
% 5.46/3.00  Main loop            : 1.37
% 5.46/3.00  Inferencing          : 0.51
% 5.46/3.00  Reduction            : 0.36
% 5.46/3.00  Demodulation         : 0.20
% 5.46/3.00  BG Simplification    : 0.05
% 5.46/3.00  Subsumption          : 0.35
% 5.46/3.00  Abstraction          : 0.07
% 5.46/3.00  MUC search           : 0.00
% 5.46/3.00  Cooper               : 0.00
% 5.46/3.00  Total                : 2.08
% 5.46/3.00  Index Insertion      : 0.00
% 5.46/3.00  Index Deletion       : 0.00
% 5.46/3.00  Index Matching       : 0.00
% 5.46/3.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------

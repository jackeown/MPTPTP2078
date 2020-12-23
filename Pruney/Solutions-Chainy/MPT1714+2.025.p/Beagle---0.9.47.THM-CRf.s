%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:36 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 236 expanded)
%              Number of leaves         :   33 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 ( 852 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

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

tff(c_1492,plain,(
    ! [B_243,A_244] :
      ( l1_pre_topc(B_243)
      | ~ m1_pre_topc(B_243,A_244)
      | ~ l1_pre_topc(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1495,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1492])).

tff(c_1507,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1495])).

tff(c_32,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1498,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1492])).

tff(c_1510,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1498])).

tff(c_54,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1408,plain,(
    ! [B_218,A_219] :
      ( l1_pre_topc(B_218)
      | ~ m1_pre_topc(B_218,A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1420,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1408])).

tff(c_1430,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1420])).

tff(c_1411,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1408])).

tff(c_1423,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1411])).

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

tff(c_126,plain,(
    ! [B_61,A_62] :
      ( r1_tsep_1(B_61,A_62)
      | ~ r1_tsep_1(A_62,B_61)
      | ~ l1_struct_0(B_61)
      | ~ l1_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_129,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_69,c_126])).

tff(c_130,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_133,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_130])).

tff(c_137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_133])).

tff(c_138,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_140,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_143,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_143])).

tff(c_149,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_139,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_150,plain,(
    ! [B_63,A_64] :
      ( m1_subset_1(u1_struct_0(B_63),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_pre_topc(B_63,A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_160,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0(A_66))
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_150,c_28])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_164,plain,(
    ! [B_65,A_66] :
      ( k3_xboole_0(u1_struct_0(B_65),u1_struct_0(A_66)) = u1_struct_0(B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_160,c_26])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_114,plain,(
    ! [D_55,B_56,A_57] :
      ( r2_hidden(D_55,B_56)
      | ~ r2_hidden(D_55,k3_xboole_0(A_57,B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_123,plain,(
    ! [A_57,B_56,B_8] :
      ( r2_hidden('#skF_3'(k3_xboole_0(A_57,B_56),B_8),B_56)
      | r1_xboole_0(k3_xboole_0(A_57,B_56),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_174,plain,(
    ! [A_70,B_71] :
      ( r1_xboole_0(u1_struct_0(A_70),u1_struct_0(B_71))
      | ~ r1_tsep_1(A_70,B_71)
      | ~ l1_struct_0(B_71)
      | ~ l1_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_311,plain,(
    ! [C_94,B_95,A_96] :
      ( ~ r2_hidden(C_94,u1_struct_0(B_95))
      | ~ r2_hidden(C_94,u1_struct_0(A_96))
      | ~ r1_tsep_1(A_96,B_95)
      | ~ l1_struct_0(B_95)
      | ~ l1_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_174,c_20])).

tff(c_1006,plain,(
    ! [A_170,B_171,A_172] :
      ( ~ r2_hidden('#skF_3'(A_170,u1_struct_0(B_171)),u1_struct_0(A_172))
      | ~ r1_tsep_1(A_172,B_171)
      | ~ l1_struct_0(B_171)
      | ~ l1_struct_0(A_172)
      | r1_xboole_0(A_170,u1_struct_0(B_171)) ) ),
    inference(resolution,[status(thm)],[c_22,c_311])).

tff(c_1068,plain,(
    ! [A_178,B_179,A_180] :
      ( ~ r1_tsep_1(A_178,B_179)
      | ~ l1_struct_0(B_179)
      | ~ l1_struct_0(A_178)
      | r1_xboole_0(k3_xboole_0(A_180,u1_struct_0(A_178)),u1_struct_0(B_179)) ) ),
    inference(resolution,[status(thm)],[c_123,c_1006])).

tff(c_1250,plain,(
    ! [A_207,B_208,B_209] :
      ( ~ r1_tsep_1(A_207,B_208)
      | ~ l1_struct_0(B_208)
      | ~ l1_struct_0(A_207)
      | r1_xboole_0(u1_struct_0(B_209),u1_struct_0(B_208))
      | ~ m1_pre_topc(B_209,A_207)
      | ~ l1_pre_topc(A_207) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_1068])).

tff(c_1254,plain,(
    ! [B_209] :
      ( ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0('#skF_6')
      | r1_xboole_0(u1_struct_0(B_209),u1_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_209,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_69,c_1250])).

tff(c_1339,plain,(
    ! [B_215] :
      ( r1_xboole_0(u1_struct_0(B_215),u1_struct_0('#skF_7'))
      | ~ m1_pre_topc(B_215,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_139,c_149,c_1254])).

tff(c_36,plain,(
    ! [A_20,B_22] :
      ( r1_tsep_1(A_20,B_22)
      | ~ r1_xboole_0(u1_struct_0(A_20),u1_struct_0(B_22))
      | ~ l1_struct_0(B_22)
      | ~ l1_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1342,plain,(
    ! [B_215] :
      ( r1_tsep_1(B_215,'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(B_215)
      | ~ m1_pre_topc(B_215,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1339,c_36])).

tff(c_1371,plain,(
    ! [B_217] :
      ( r1_tsep_1(B_217,'#skF_7')
      | ~ l1_struct_0(B_217)
      | ~ m1_pre_topc(B_217,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1342])).

tff(c_46,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_68,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_1383,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1371,c_68])).

tff(c_1398,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1383])).

tff(c_1401,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_1398])).

tff(c_1405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1401])).

tff(c_1407,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1406,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1465,plain,(
    ! [B_239,A_240] :
      ( r1_tsep_1(B_239,A_240)
      | ~ r1_tsep_1(A_240,B_239)
      | ~ l1_struct_0(B_239)
      | ~ l1_struct_0(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1467,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1406,c_1465])).

tff(c_1470,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1407,c_1467])).

tff(c_1471,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1470])).

tff(c_1474,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1471])).

tff(c_1478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1423,c_1474])).

tff(c_1479,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1470])).

tff(c_1483,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_1479])).

tff(c_1487,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1430,c_1483])).

tff(c_1488,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1489,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1548,plain,(
    ! [B_262,A_263] :
      ( r1_tsep_1(B_262,A_263)
      | ~ r1_tsep_1(A_263,B_262)
      | ~ l1_struct_0(B_262)
      | ~ l1_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1552,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1489,c_1548])).

tff(c_1556,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1488,c_1552])).

tff(c_1557,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1556])).

tff(c_1561,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_1557])).

tff(c_1565,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1561])).

tff(c_1566,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1556])).

tff(c_1570,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_1566])).

tff(c_1574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_1570])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.93/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.65  
% 3.93/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.65  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.93/1.65  
% 3.93/1.65  %Foreground sorts:
% 3.93/1.65  
% 3.93/1.65  
% 3.93/1.65  %Background operators:
% 3.93/1.65  
% 3.93/1.65  
% 3.93/1.65  %Foreground operators:
% 3.93/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.93/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.93/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.93/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.93/1.65  tff('#skF_7', type, '#skF_7': $i).
% 3.93/1.65  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.93/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.93/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.93/1.65  tff('#skF_6', type, '#skF_6': $i).
% 3.93/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.93/1.65  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.93/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.93/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.93/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.93/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.93/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.93/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.93/1.65  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.93/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.93/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.93/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.93/1.65  
% 3.93/1.67  tff(f_133, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.93/1.67  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.93/1.67  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.93/1.67  tff(f_88, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.93/1.67  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.93/1.67  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.93/1.67  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.93/1.67  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.93/1.67  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.93/1.67  tff(f_80, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.93/1.67  tff(c_62, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.67  tff(c_50, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.67  tff(c_1492, plain, (![B_243, A_244]: (l1_pre_topc(B_243) | ~m1_pre_topc(B_243, A_244) | ~l1_pre_topc(A_244))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.67  tff(c_1495, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1492])).
% 3.93/1.67  tff(c_1507, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1495])).
% 3.93/1.67  tff(c_32, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.93/1.67  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.67  tff(c_1498, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1492])).
% 3.93/1.67  tff(c_1510, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1498])).
% 3.93/1.67  tff(c_54, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.67  tff(c_1408, plain, (![B_218, A_219]: (l1_pre_topc(B_218) | ~m1_pre_topc(B_218, A_219) | ~l1_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.67  tff(c_1420, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1408])).
% 3.93/1.67  tff(c_1430, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1420])).
% 3.93/1.67  tff(c_1411, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1408])).
% 3.93/1.67  tff(c_1423, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1411])).
% 3.93/1.67  tff(c_71, plain, (![B_42, A_43]: (l1_pre_topc(B_42) | ~m1_pre_topc(B_42, A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.93/1.67  tff(c_77, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_71])).
% 3.93/1.67  tff(c_89, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_77])).
% 3.93/1.67  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.67  tff(c_74, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_50, c_71])).
% 3.93/1.67  tff(c_86, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_74])).
% 3.93/1.67  tff(c_83, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_71])).
% 3.93/1.67  tff(c_93, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_83])).
% 3.93/1.67  tff(c_44, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.67  tff(c_69, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_44])).
% 3.93/1.67  tff(c_126, plain, (![B_61, A_62]: (r1_tsep_1(B_61, A_62) | ~r1_tsep_1(A_62, B_61) | ~l1_struct_0(B_61) | ~l1_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.93/1.67  tff(c_129, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_69, c_126])).
% 3.93/1.67  tff(c_130, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_129])).
% 3.93/1.67  tff(c_133, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_32, c_130])).
% 3.93/1.67  tff(c_137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_133])).
% 3.93/1.67  tff(c_138, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_129])).
% 3.93/1.67  tff(c_140, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_138])).
% 3.93/1.67  tff(c_143, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_140])).
% 3.93/1.67  tff(c_147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_143])).
% 3.93/1.67  tff(c_149, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_138])).
% 3.93/1.67  tff(c_139, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_129])).
% 3.93/1.67  tff(c_150, plain, (![B_63, A_64]: (m1_subset_1(u1_struct_0(B_63), k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_pre_topc(B_63, A_64) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.93/1.67  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.93/1.67  tff(c_160, plain, (![B_65, A_66]: (r1_tarski(u1_struct_0(B_65), u1_struct_0(A_66)) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_150, c_28])).
% 3.93/1.67  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.93/1.67  tff(c_164, plain, (![B_65, A_66]: (k3_xboole_0(u1_struct_0(B_65), u1_struct_0(A_66))=u1_struct_0(B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_160, c_26])).
% 3.93/1.67  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.93/1.67  tff(c_114, plain, (![D_55, B_56, A_57]: (r2_hidden(D_55, B_56) | ~r2_hidden(D_55, k3_xboole_0(A_57, B_56)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.93/1.67  tff(c_123, plain, (![A_57, B_56, B_8]: (r2_hidden('#skF_3'(k3_xboole_0(A_57, B_56), B_8), B_56) | r1_xboole_0(k3_xboole_0(A_57, B_56), B_8))), inference(resolution, [status(thm)], [c_24, c_114])).
% 3.93/1.67  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.93/1.67  tff(c_174, plain, (![A_70, B_71]: (r1_xboole_0(u1_struct_0(A_70), u1_struct_0(B_71)) | ~r1_tsep_1(A_70, B_71) | ~l1_struct_0(B_71) | ~l1_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.93/1.67  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.93/1.67  tff(c_311, plain, (![C_94, B_95, A_96]: (~r2_hidden(C_94, u1_struct_0(B_95)) | ~r2_hidden(C_94, u1_struct_0(A_96)) | ~r1_tsep_1(A_96, B_95) | ~l1_struct_0(B_95) | ~l1_struct_0(A_96))), inference(resolution, [status(thm)], [c_174, c_20])).
% 3.93/1.67  tff(c_1006, plain, (![A_170, B_171, A_172]: (~r2_hidden('#skF_3'(A_170, u1_struct_0(B_171)), u1_struct_0(A_172)) | ~r1_tsep_1(A_172, B_171) | ~l1_struct_0(B_171) | ~l1_struct_0(A_172) | r1_xboole_0(A_170, u1_struct_0(B_171)))), inference(resolution, [status(thm)], [c_22, c_311])).
% 3.93/1.67  tff(c_1068, plain, (![A_178, B_179, A_180]: (~r1_tsep_1(A_178, B_179) | ~l1_struct_0(B_179) | ~l1_struct_0(A_178) | r1_xboole_0(k3_xboole_0(A_180, u1_struct_0(A_178)), u1_struct_0(B_179)))), inference(resolution, [status(thm)], [c_123, c_1006])).
% 3.93/1.67  tff(c_1250, plain, (![A_207, B_208, B_209]: (~r1_tsep_1(A_207, B_208) | ~l1_struct_0(B_208) | ~l1_struct_0(A_207) | r1_xboole_0(u1_struct_0(B_209), u1_struct_0(B_208)) | ~m1_pre_topc(B_209, A_207) | ~l1_pre_topc(A_207))), inference(superposition, [status(thm), theory('equality')], [c_164, c_1068])).
% 3.93/1.67  tff(c_1254, plain, (![B_209]: (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | r1_xboole_0(u1_struct_0(B_209), u1_struct_0('#skF_7')) | ~m1_pre_topc(B_209, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_69, c_1250])).
% 3.93/1.67  tff(c_1339, plain, (![B_215]: (r1_xboole_0(u1_struct_0(B_215), u1_struct_0('#skF_7')) | ~m1_pre_topc(B_215, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_139, c_149, c_1254])).
% 3.93/1.67  tff(c_36, plain, (![A_20, B_22]: (r1_tsep_1(A_20, B_22) | ~r1_xboole_0(u1_struct_0(A_20), u1_struct_0(B_22)) | ~l1_struct_0(B_22) | ~l1_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.93/1.67  tff(c_1342, plain, (![B_215]: (r1_tsep_1(B_215, '#skF_7') | ~l1_struct_0('#skF_7') | ~l1_struct_0(B_215) | ~m1_pre_topc(B_215, '#skF_6'))), inference(resolution, [status(thm)], [c_1339, c_36])).
% 3.93/1.67  tff(c_1371, plain, (![B_217]: (r1_tsep_1(B_217, '#skF_7') | ~l1_struct_0(B_217) | ~m1_pre_topc(B_217, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1342])).
% 3.93/1.67  tff(c_46, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.93/1.67  tff(c_68, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_46])).
% 3.93/1.67  tff(c_1383, plain, (~l1_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1371, c_68])).
% 3.93/1.67  tff(c_1398, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1383])).
% 3.93/1.67  tff(c_1401, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_32, c_1398])).
% 3.93/1.67  tff(c_1405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_1401])).
% 3.93/1.67  tff(c_1407, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_44])).
% 3.93/1.67  tff(c_1406, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_44])).
% 3.93/1.67  tff(c_1465, plain, (![B_239, A_240]: (r1_tsep_1(B_239, A_240) | ~r1_tsep_1(A_240, B_239) | ~l1_struct_0(B_239) | ~l1_struct_0(A_240))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.93/1.67  tff(c_1467, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1406, c_1465])).
% 3.93/1.67  tff(c_1470, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1407, c_1467])).
% 3.93/1.67  tff(c_1471, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1470])).
% 3.93/1.67  tff(c_1474, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1471])).
% 3.93/1.67  tff(c_1478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1423, c_1474])).
% 3.93/1.67  tff(c_1479, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1470])).
% 3.93/1.67  tff(c_1483, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_32, c_1479])).
% 3.93/1.67  tff(c_1487, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1430, c_1483])).
% 3.93/1.67  tff(c_1488, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 3.93/1.67  tff(c_1489, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 3.93/1.67  tff(c_1548, plain, (![B_262, A_263]: (r1_tsep_1(B_262, A_263) | ~r1_tsep_1(A_263, B_262) | ~l1_struct_0(B_262) | ~l1_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.93/1.67  tff(c_1552, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1489, c_1548])).
% 3.93/1.67  tff(c_1556, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1488, c_1552])).
% 3.93/1.67  tff(c_1557, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1556])).
% 3.93/1.67  tff(c_1561, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_32, c_1557])).
% 3.93/1.67  tff(c_1565, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1561])).
% 3.93/1.67  tff(c_1566, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_1556])).
% 3.93/1.67  tff(c_1570, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_32, c_1566])).
% 3.93/1.67  tff(c_1574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1507, c_1570])).
% 3.93/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/1.67  
% 3.93/1.67  Inference rules
% 3.93/1.67  ----------------------
% 3.93/1.67  #Ref     : 0
% 3.93/1.67  #Sup     : 319
% 3.93/1.67  #Fact    : 0
% 3.93/1.67  #Define  : 0
% 3.93/1.67  #Split   : 10
% 3.93/1.67  #Chain   : 0
% 3.93/1.67  #Close   : 0
% 3.93/1.67  
% 3.93/1.67  Ordering : KBO
% 3.93/1.67  
% 3.93/1.67  Simplification rules
% 3.93/1.67  ----------------------
% 3.93/1.67  #Subsume      : 64
% 3.93/1.67  #Demod        : 95
% 3.93/1.67  #Tautology    : 24
% 3.93/1.67  #SimpNegUnit  : 2
% 3.93/1.67  #BackRed      : 0
% 3.93/1.67  
% 3.93/1.67  #Partial instantiations: 0
% 3.93/1.67  #Strategies tried      : 1
% 3.93/1.67  
% 3.93/1.67  Timing (in seconds)
% 3.93/1.67  ----------------------
% 3.93/1.67  Preprocessing        : 0.32
% 3.93/1.67  Parsing              : 0.17
% 3.93/1.67  CNF conversion       : 0.03
% 3.93/1.67  Main loop            : 0.57
% 3.93/1.67  Inferencing          : 0.22
% 3.93/1.67  Reduction            : 0.13
% 3.93/1.67  Demodulation         : 0.09
% 3.93/1.67  BG Simplification    : 0.03
% 3.93/1.67  Subsumption          : 0.13
% 3.93/1.67  Abstraction          : 0.03
% 3.93/1.67  MUC search           : 0.00
% 3.93/1.67  Cooper               : 0.00
% 3.93/1.67  Total                : 0.92
% 3.93/1.67  Index Insertion      : 0.00
% 3.93/1.67  Index Deletion       : 0.00
% 3.93/1.67  Index Matching       : 0.00
% 3.93/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------

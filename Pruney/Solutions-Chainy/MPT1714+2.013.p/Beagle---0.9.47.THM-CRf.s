%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:34 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 277 expanded)
%              Number of leaves         :   35 ( 101 expanded)
%              Depth                    :   19
%              Number of atoms          :  243 ( 968 expanded)
%              Number of equality atoms :    8 (  16 expanded)
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

tff(f_143,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(c_70,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1992,plain,(
    ! [B_242,A_243] :
      ( l1_pre_topc(B_242)
      | ~ m1_pre_topc(B_242,A_243)
      | ~ l1_pre_topc(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1995,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1992])).

tff(c_2007,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1995])).

tff(c_40,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_66,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1998,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1992])).

tff(c_2010,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1998])).

tff(c_62,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1920,plain,(
    ! [B_217,A_218] :
      ( l1_pre_topc(B_217)
      | ~ m1_pre_topc(B_217,A_218)
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1932,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1920])).

tff(c_1942,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1932])).

tff(c_1923,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1920])).

tff(c_1935,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1923])).

tff(c_82,plain,(
    ! [B_50,A_51] :
      ( l1_pre_topc(B_50)
      | ~ m1_pre_topc(B_50,A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_82])).

tff(c_104,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_94])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_82])).

tff(c_105,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_105])).

tff(c_108,plain,(
    l1_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_181,plain,(
    ! [B_76,A_77] :
      ( m1_subset_1(u1_struct_0(B_76),k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_185,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(u1_struct_0(B_76),u1_struct_0(A_77))
      | ~ m1_pre_topc(B_76,A_77)
      | ~ l1_pre_topc(A_77) ) ),
    inference(resolution,[status(thm)],[c_181,c_36])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_82])).

tff(c_97,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_85])).

tff(c_52,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_80,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_133,plain,(
    ! [B_71,A_72] :
      ( r1_tsep_1(B_71,A_72)
      | ~ r1_tsep_1(A_72,B_71)
      | ~ l1_struct_0(B_71)
      | ~ l1_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_136,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_133])).

tff(c_137,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_140,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_137])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_140])).

tff(c_145,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_147,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_150,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_147])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_150])).

tff(c_156,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_146,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_190,plain,(
    ! [A_80,C_81,B_82] :
      ( r1_tarski(k2_xboole_0(A_80,C_81),B_82)
      | ~ r1_tarski(C_81,B_82)
      | ~ r1_tarski(A_80,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_121,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_126,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),A_14) ) ),
    inference(resolution,[status(thm)],[c_32,c_121])).

tff(c_194,plain,(
    ! [B_82,C_81] :
      ( k2_xboole_0(B_82,C_81) = B_82
      | ~ r1_tarski(C_81,B_82)
      | ~ r1_tarski(B_82,B_82) ) ),
    inference(resolution,[status(thm)],[c_190,c_126])).

tff(c_205,plain,(
    ! [B_85,C_86] :
      ( k2_xboole_0(B_85,C_86) = B_85
      | ~ r1_tarski(C_86,B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_194])).

tff(c_221,plain,(
    ! [B_13] : k2_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_205])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(k2_xboole_0(A_16,C_18),B_17)
      | ~ r1_tarski(C_18,B_17)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_352,plain,(
    ! [B_97,A_98,C_99] :
      ( k2_xboole_0(B_97,k2_xboole_0(A_98,C_99)) = B_97
      | ~ r1_tarski(C_99,B_97)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(resolution,[status(thm)],[c_34,c_205])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_490,plain,(
    ! [D_113,A_114,C_115,B_116] :
      ( ~ r2_hidden(D_113,k2_xboole_0(A_114,C_115))
      | r2_hidden(D_113,B_116)
      | ~ r1_tarski(C_115,B_116)
      | ~ r1_tarski(A_114,B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_4])).

tff(c_513,plain,(
    ! [D_117,B_118,B_119] :
      ( ~ r2_hidden(D_117,B_118)
      | r2_hidden(D_117,B_119)
      | ~ r1_tarski(B_118,B_119)
      | ~ r1_tarski(B_118,B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_490])).

tff(c_525,plain,(
    ! [A_7,B_8,B_119] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_119)
      | ~ r1_tarski(A_7,B_119)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_513])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_201,plain,(
    ! [A_83,B_84] :
      ( r1_xboole_0(u1_struct_0(A_83),u1_struct_0(B_84))
      | ~ r1_tsep_1(A_83,B_84)
      | ~ l1_struct_0(B_84)
      | ~ l1_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1028,plain,(
    ! [C_161,B_162,A_163] :
      ( ~ r2_hidden(C_161,u1_struct_0(B_162))
      | ~ r2_hidden(C_161,u1_struct_0(A_163))
      | ~ r1_tsep_1(A_163,B_162)
      | ~ l1_struct_0(B_162)
      | ~ l1_struct_0(A_163) ) ),
    inference(resolution,[status(thm)],[c_201,c_20])).

tff(c_1572,plain,(
    ! [A_197,B_198,A_199] :
      ( ~ r2_hidden('#skF_3'(A_197,u1_struct_0(B_198)),u1_struct_0(A_199))
      | ~ r1_tsep_1(A_199,B_198)
      | ~ l1_struct_0(B_198)
      | ~ l1_struct_0(A_199)
      | r1_xboole_0(A_197,u1_struct_0(B_198)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1028])).

tff(c_1603,plain,(
    ! [A_202,B_203,A_204] :
      ( ~ r1_tsep_1(A_202,B_203)
      | ~ l1_struct_0(B_203)
      | ~ l1_struct_0(A_202)
      | ~ r1_tarski(A_204,u1_struct_0(A_202))
      | r1_xboole_0(A_204,u1_struct_0(B_203)) ) ),
    inference(resolution,[status(thm)],[c_525,c_1572])).

tff(c_1607,plain,(
    ! [A_204] :
      ( ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0('#skF_6')
      | ~ r1_tarski(A_204,u1_struct_0('#skF_6'))
      | r1_xboole_0(A_204,u1_struct_0('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_80,c_1603])).

tff(c_1625,plain,(
    ! [A_206] :
      ( ~ r1_tarski(A_206,u1_struct_0('#skF_6'))
      | r1_xboole_0(A_206,u1_struct_0('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_156,c_1607])).

tff(c_44,plain,(
    ! [A_25,B_27] :
      ( r1_tsep_1(A_25,B_27)
      | ~ r1_xboole_0(u1_struct_0(A_25),u1_struct_0(B_27))
      | ~ l1_struct_0(B_27)
      | ~ l1_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1629,plain,(
    ! [A_25] :
      ( r1_tsep_1(A_25,'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_25)
      | ~ r1_tarski(u1_struct_0(A_25),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1625,c_44])).

tff(c_1873,plain,(
    ! [A_215] :
      ( r1_tsep_1(A_215,'#skF_7')
      | ~ l1_struct_0(A_215)
      | ~ r1_tarski(u1_struct_0(A_215),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1629])).

tff(c_1877,plain,(
    ! [B_76] :
      ( r1_tsep_1(B_76,'#skF_7')
      | ~ l1_struct_0(B_76)
      | ~ m1_pre_topc(B_76,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_185,c_1873])).

tff(c_1888,plain,(
    ! [B_216] :
      ( r1_tsep_1(B_216,'#skF_7')
      | ~ l1_struct_0(B_216)
      | ~ m1_pre_topc(B_216,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1877])).

tff(c_54,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_79,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1898,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1888,c_79])).

tff(c_1910,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1898])).

tff(c_1913,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1910])).

tff(c_1917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_1913])).

tff(c_1919,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1918,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1965,plain,(
    ! [B_238,A_239] :
      ( r1_tsep_1(B_238,A_239)
      | ~ r1_tsep_1(A_239,B_238)
      | ~ l1_struct_0(B_238)
      | ~ l1_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1967,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1918,c_1965])).

tff(c_1970,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_1919,c_1967])).

tff(c_1971,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1970])).

tff(c_1974,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_1971])).

tff(c_1978,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_1974])).

tff(c_1979,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1970])).

tff(c_1983,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_1979])).

tff(c_1987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1942,c_1983])).

tff(c_1988,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1989,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2038,plain,(
    ! [B_263,A_264] :
      ( r1_tsep_1(B_263,A_264)
      | ~ r1_tsep_1(A_264,B_263)
      | ~ l1_struct_0(B_263)
      | ~ l1_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2042,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1989,c_2038])).

tff(c_2046,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_1988,c_2042])).

tff(c_2047,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2046])).

tff(c_2050,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_2047])).

tff(c_2054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2010,c_2050])).

tff(c_2055,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2046])).

tff(c_2070,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_40,c_2055])).

tff(c_2074,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2007,c_2070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:44:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.84  
% 4.64/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.84  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.64/1.84  
% 4.64/1.84  %Foreground sorts:
% 4.64/1.84  
% 4.64/1.84  
% 4.64/1.84  %Background operators:
% 4.64/1.84  
% 4.64/1.84  
% 4.64/1.84  %Foreground operators:
% 4.64/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.64/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.64/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.64/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.64/1.84  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.64/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.64/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.64/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.64/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.64/1.84  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.84  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.64/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.64/1.84  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.64/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.64/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.64/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.84  
% 4.64/1.86  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 4.64/1.86  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.64/1.86  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.64/1.86  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.64/1.86  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.64/1.86  tff(f_98, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 4.64/1.86  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.64/1.86  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.64/1.86  tff(f_66, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.64/1.86  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.64/1.86  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.64/1.86  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 4.64/1.86  tff(c_70, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.64/1.86  tff(c_58, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.64/1.86  tff(c_1992, plain, (![B_242, A_243]: (l1_pre_topc(B_242) | ~m1_pre_topc(B_242, A_243) | ~l1_pre_topc(A_243))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.64/1.86  tff(c_1995, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1992])).
% 4.64/1.86  tff(c_2007, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1995])).
% 4.64/1.86  tff(c_40, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.64/1.86  tff(c_66, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.64/1.86  tff(c_1998, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1992])).
% 4.64/1.86  tff(c_2010, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1998])).
% 4.64/1.86  tff(c_62, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.64/1.86  tff(c_1920, plain, (![B_217, A_218]: (l1_pre_topc(B_217) | ~m1_pre_topc(B_217, A_218) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.64/1.86  tff(c_1932, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_62, c_1920])).
% 4.64/1.86  tff(c_1942, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1932])).
% 4.64/1.86  tff(c_1923, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_1920])).
% 4.64/1.86  tff(c_1935, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1923])).
% 4.64/1.86  tff(c_82, plain, (![B_50, A_51]: (l1_pre_topc(B_50) | ~m1_pre_topc(B_50, A_51) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.64/1.86  tff(c_94, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_62, c_82])).
% 4.64/1.86  tff(c_104, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_94])).
% 4.64/1.86  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.64/1.86  tff(c_101, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_56, c_82])).
% 4.64/1.86  tff(c_105, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_101])).
% 4.64/1.86  tff(c_107, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_105])).
% 4.64/1.86  tff(c_108, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_101])).
% 4.64/1.86  tff(c_181, plain, (![B_76, A_77]: (m1_subset_1(u1_struct_0(B_76), k1_zfmisc_1(u1_struct_0(A_77))) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.64/1.86  tff(c_36, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.64/1.86  tff(c_185, plain, (![B_76, A_77]: (r1_tarski(u1_struct_0(B_76), u1_struct_0(A_77)) | ~m1_pre_topc(B_76, A_77) | ~l1_pre_topc(A_77))), inference(resolution, [status(thm)], [c_181, c_36])).
% 4.64/1.86  tff(c_85, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_82])).
% 4.64/1.86  tff(c_97, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_85])).
% 4.64/1.86  tff(c_52, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.64/1.86  tff(c_80, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 4.64/1.86  tff(c_133, plain, (![B_71, A_72]: (r1_tsep_1(B_71, A_72) | ~r1_tsep_1(A_72, B_71) | ~l1_struct_0(B_71) | ~l1_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.64/1.86  tff(c_136, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_80, c_133])).
% 4.64/1.86  tff(c_137, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_136])).
% 4.64/1.86  tff(c_140, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_137])).
% 4.64/1.86  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_140])).
% 4.64/1.86  tff(c_145, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_136])).
% 4.64/1.86  tff(c_147, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_145])).
% 4.64/1.86  tff(c_150, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_147])).
% 4.64/1.86  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_150])).
% 4.64/1.86  tff(c_156, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_145])).
% 4.64/1.86  tff(c_146, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_136])).
% 4.64/1.86  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.64/1.86  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.64/1.86  tff(c_190, plain, (![A_80, C_81, B_82]: (r1_tarski(k2_xboole_0(A_80, C_81), B_82) | ~r1_tarski(C_81, B_82) | ~r1_tarski(A_80, B_82))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.64/1.86  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.64/1.86  tff(c_121, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.64/1.86  tff(c_126, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(k2_xboole_0(A_14, B_15), A_14))), inference(resolution, [status(thm)], [c_32, c_121])).
% 4.64/1.86  tff(c_194, plain, (![B_82, C_81]: (k2_xboole_0(B_82, C_81)=B_82 | ~r1_tarski(C_81, B_82) | ~r1_tarski(B_82, B_82))), inference(resolution, [status(thm)], [c_190, c_126])).
% 4.64/1.86  tff(c_205, plain, (![B_85, C_86]: (k2_xboole_0(B_85, C_86)=B_85 | ~r1_tarski(C_86, B_85))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_194])).
% 4.64/1.86  tff(c_221, plain, (![B_13]: (k2_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_205])).
% 4.64/1.86  tff(c_34, plain, (![A_16, C_18, B_17]: (r1_tarski(k2_xboole_0(A_16, C_18), B_17) | ~r1_tarski(C_18, B_17) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.64/1.86  tff(c_352, plain, (![B_97, A_98, C_99]: (k2_xboole_0(B_97, k2_xboole_0(A_98, C_99))=B_97 | ~r1_tarski(C_99, B_97) | ~r1_tarski(A_98, B_97))), inference(resolution, [status(thm)], [c_34, c_205])).
% 4.64/1.86  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.64/1.86  tff(c_490, plain, (![D_113, A_114, C_115, B_116]: (~r2_hidden(D_113, k2_xboole_0(A_114, C_115)) | r2_hidden(D_113, B_116) | ~r1_tarski(C_115, B_116) | ~r1_tarski(A_114, B_116))), inference(superposition, [status(thm), theory('equality')], [c_352, c_4])).
% 4.64/1.86  tff(c_513, plain, (![D_117, B_118, B_119]: (~r2_hidden(D_117, B_118) | r2_hidden(D_117, B_119) | ~r1_tarski(B_118, B_119) | ~r1_tarski(B_118, B_119))), inference(superposition, [status(thm), theory('equality')], [c_221, c_490])).
% 4.64/1.86  tff(c_525, plain, (![A_7, B_8, B_119]: (r2_hidden('#skF_3'(A_7, B_8), B_119) | ~r1_tarski(A_7, B_119) | r1_xboole_0(A_7, B_8))), inference(resolution, [status(thm)], [c_24, c_513])).
% 4.64/1.86  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.64/1.86  tff(c_201, plain, (![A_83, B_84]: (r1_xboole_0(u1_struct_0(A_83), u1_struct_0(B_84)) | ~r1_tsep_1(A_83, B_84) | ~l1_struct_0(B_84) | ~l1_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.64/1.86  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.64/1.86  tff(c_1028, plain, (![C_161, B_162, A_163]: (~r2_hidden(C_161, u1_struct_0(B_162)) | ~r2_hidden(C_161, u1_struct_0(A_163)) | ~r1_tsep_1(A_163, B_162) | ~l1_struct_0(B_162) | ~l1_struct_0(A_163))), inference(resolution, [status(thm)], [c_201, c_20])).
% 4.64/1.86  tff(c_1572, plain, (![A_197, B_198, A_199]: (~r2_hidden('#skF_3'(A_197, u1_struct_0(B_198)), u1_struct_0(A_199)) | ~r1_tsep_1(A_199, B_198) | ~l1_struct_0(B_198) | ~l1_struct_0(A_199) | r1_xboole_0(A_197, u1_struct_0(B_198)))), inference(resolution, [status(thm)], [c_22, c_1028])).
% 4.64/1.86  tff(c_1603, plain, (![A_202, B_203, A_204]: (~r1_tsep_1(A_202, B_203) | ~l1_struct_0(B_203) | ~l1_struct_0(A_202) | ~r1_tarski(A_204, u1_struct_0(A_202)) | r1_xboole_0(A_204, u1_struct_0(B_203)))), inference(resolution, [status(thm)], [c_525, c_1572])).
% 4.64/1.86  tff(c_1607, plain, (![A_204]: (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | ~r1_tarski(A_204, u1_struct_0('#skF_6')) | r1_xboole_0(A_204, u1_struct_0('#skF_7')))), inference(resolution, [status(thm)], [c_80, c_1603])).
% 4.64/1.86  tff(c_1625, plain, (![A_206]: (~r1_tarski(A_206, u1_struct_0('#skF_6')) | r1_xboole_0(A_206, u1_struct_0('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_156, c_1607])).
% 4.64/1.86  tff(c_44, plain, (![A_25, B_27]: (r1_tsep_1(A_25, B_27) | ~r1_xboole_0(u1_struct_0(A_25), u1_struct_0(B_27)) | ~l1_struct_0(B_27) | ~l1_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.64/1.86  tff(c_1629, plain, (![A_25]: (r1_tsep_1(A_25, '#skF_7') | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_25) | ~r1_tarski(u1_struct_0(A_25), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1625, c_44])).
% 4.64/1.86  tff(c_1873, plain, (![A_215]: (r1_tsep_1(A_215, '#skF_7') | ~l1_struct_0(A_215) | ~r1_tarski(u1_struct_0(A_215), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1629])).
% 4.64/1.86  tff(c_1877, plain, (![B_76]: (r1_tsep_1(B_76, '#skF_7') | ~l1_struct_0(B_76) | ~m1_pre_topc(B_76, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_185, c_1873])).
% 4.64/1.86  tff(c_1888, plain, (![B_216]: (r1_tsep_1(B_216, '#skF_7') | ~l1_struct_0(B_216) | ~m1_pre_topc(B_216, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1877])).
% 4.64/1.86  tff(c_54, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.64/1.86  tff(c_79, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_54])).
% 4.64/1.86  tff(c_1898, plain, (~l1_struct_0('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1888, c_79])).
% 4.64/1.86  tff(c_1910, plain, (~l1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1898])).
% 4.64/1.86  tff(c_1913, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1910])).
% 4.64/1.86  tff(c_1917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_1913])).
% 4.64/1.86  tff(c_1919, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_52])).
% 4.64/1.86  tff(c_1918, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_52])).
% 4.64/1.86  tff(c_1965, plain, (![B_238, A_239]: (r1_tsep_1(B_238, A_239) | ~r1_tsep_1(A_239, B_238) | ~l1_struct_0(B_238) | ~l1_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.64/1.86  tff(c_1967, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1918, c_1965])).
% 4.64/1.86  tff(c_1970, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_1919, c_1967])).
% 4.64/1.86  tff(c_1971, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1970])).
% 4.64/1.86  tff(c_1974, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_1971])).
% 4.64/1.86  tff(c_1978, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1935, c_1974])).
% 4.64/1.86  tff(c_1979, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1970])).
% 4.64/1.86  tff(c_1983, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_40, c_1979])).
% 4.64/1.86  tff(c_1987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1942, c_1983])).
% 4.64/1.86  tff(c_1988, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_54])).
% 4.64/1.86  tff(c_1989, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 4.64/1.86  tff(c_2038, plain, (![B_263, A_264]: (r1_tsep_1(B_263, A_264) | ~r1_tsep_1(A_264, B_263) | ~l1_struct_0(B_263) | ~l1_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.64/1.86  tff(c_2042, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1989, c_2038])).
% 4.64/1.86  tff(c_2046, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_1988, c_2042])).
% 4.64/1.86  tff(c_2047, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2046])).
% 4.64/1.86  tff(c_2050, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_2047])).
% 4.64/1.86  tff(c_2054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2010, c_2050])).
% 4.64/1.86  tff(c_2055, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_2046])).
% 4.64/1.86  tff(c_2070, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_40, c_2055])).
% 4.64/1.86  tff(c_2074, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2007, c_2070])).
% 4.64/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.64/1.86  
% 4.64/1.86  Inference rules
% 4.64/1.86  ----------------------
% 4.64/1.86  #Ref     : 0
% 4.64/1.86  #Sup     : 421
% 4.64/1.86  #Fact    : 10
% 4.64/1.86  #Define  : 0
% 4.64/1.86  #Split   : 13
% 4.64/1.86  #Chain   : 0
% 4.64/1.86  #Close   : 0
% 4.64/1.86  
% 4.64/1.86  Ordering : KBO
% 4.64/1.86  
% 4.64/1.86  Simplification rules
% 4.64/1.86  ----------------------
% 4.64/1.86  #Subsume      : 70
% 4.64/1.86  #Demod        : 137
% 4.64/1.86  #Tautology    : 84
% 4.64/1.86  #SimpNegUnit  : 2
% 4.64/1.86  #BackRed      : 0
% 4.64/1.86  
% 4.64/1.86  #Partial instantiations: 0
% 4.64/1.86  #Strategies tried      : 1
% 4.64/1.86  
% 4.64/1.86  Timing (in seconds)
% 4.64/1.86  ----------------------
% 4.64/1.87  Preprocessing        : 0.34
% 4.64/1.87  Parsing              : 0.18
% 4.64/1.87  CNF conversion       : 0.03
% 4.64/1.87  Main loop            : 0.70
% 4.64/1.87  Inferencing          : 0.25
% 4.64/1.87  Reduction            : 0.17
% 4.64/1.87  Demodulation         : 0.12
% 4.64/1.87  BG Simplification    : 0.03
% 4.64/1.87  Subsumption          : 0.19
% 4.64/1.87  Abstraction          : 0.03
% 4.64/1.87  MUC search           : 0.00
% 4.64/1.87  Cooper               : 0.00
% 4.64/1.87  Total                : 1.08
% 4.64/1.87  Index Insertion      : 0.00
% 4.64/1.87  Index Deletion       : 0.00
% 4.64/1.87  Index Matching       : 0.00
% 4.64/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

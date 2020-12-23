%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:33 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 277 expanded)
%              Number of leaves         :   31 ( 100 expanded)
%              Depth                    :   16
%              Number of atoms          :  263 (1056 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
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

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(c_54,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_929,plain,(
    ! [B_193,A_194] :
      ( l1_pre_topc(B_193)
      | ~ m1_pre_topc(B_193,A_194)
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_941,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_929])).

tff(c_951,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_941])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_948,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_929])).

tff(c_952,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_948])).

tff(c_954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_951,c_952])).

tff(c_956,plain,(
    l1_pre_topc('#skF_4') ),
    inference(splitRight,[status(thm)],[c_948])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_932,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_929])).

tff(c_944,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_932])).

tff(c_823,plain,(
    ! [B_169,A_170] :
      ( l1_pre_topc(B_169)
      | ~ m1_pre_topc(B_169,A_170)
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_826,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_823])).

tff(c_838,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_826])).

tff(c_50,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_829,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_823])).

tff(c_841,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_829])).

tff(c_65,plain,(
    ! [B_48,A_49] :
      ( l1_pre_topc(B_48)
      | ~ m1_pre_topc(B_48,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_71,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_65])).

tff(c_83,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_71])).

tff(c_56,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_109,plain,(
    ! [B_58,A_59] :
      ( v2_pre_topc(B_58)
      | ~ m1_pre_topc(B_58,A_59)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_121,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_109])).

tff(c_133,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_121])).

tff(c_77,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_65])).

tff(c_87,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_77])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_227,plain,(
    ! [B_85,C_86,A_87] :
      ( m1_pre_topc(B_85,C_86)
      | ~ r1_tarski(u1_struct_0(B_85),u1_struct_0(C_86))
      | ~ m1_pre_topc(C_86,A_87)
      | ~ m1_pre_topc(B_85,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_244,plain,(
    ! [B_88,A_89] :
      ( m1_pre_topc(B_88,B_88)
      | ~ m1_pre_topc(B_88,A_89)
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_12,c_227])).

tff(c_252,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_244])).

tff(c_264,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_252])).

tff(c_32,plain,(
    ! [B_30,C_32,A_26] :
      ( r1_tarski(u1_struct_0(B_30),u1_struct_0(C_32))
      | ~ m1_pre_topc(B_30,C_32)
      | ~ m1_pre_topc(C_32,A_26)
      | ~ m1_pre_topc(B_30,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_290,plain,(
    ! [B_30] :
      ( r1_tarski(u1_struct_0(B_30),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_30,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_264,c_32])).

tff(c_302,plain,(
    ! [B_30] :
      ( r1_tarski(u1_struct_0(B_30),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_30,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_87,c_290])).

tff(c_68,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_65])).

tff(c_80,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68])).

tff(c_36,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | r1_tsep_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_62,plain,(
    r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_144,plain,(
    ! [B_66,A_67] :
      ( r1_tsep_1(B_66,A_67)
      | ~ r1_tsep_1(A_67,B_66)
      | ~ l1_struct_0(B_66)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_147,plain,
    ( r1_tsep_1('#skF_5','#skF_4')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_144])).

tff(c_148,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_151,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_151])).

tff(c_156,plain,
    ( ~ l1_struct_0('#skF_5')
    | r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_158,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_161,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_161])).

tff(c_167,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_157,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_137,plain,(
    ! [C_63,A_64,B_65] :
      ( r2_hidden(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_223,plain,(
    ! [A_82,B_83,A_84] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_84)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(A_84))
      | r1_xboole_0(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_137])).

tff(c_14,plain,(
    ! [C_11,A_8,B_9] :
      ( r2_hidden(C_11,A_8)
      | ~ r2_hidden(C_11,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_489,plain,(
    ! [A_100,B_101,A_102,A_103] :
      ( r2_hidden('#skF_1'(A_100,B_101),A_102)
      | ~ m1_subset_1(A_103,k1_zfmisc_1(A_102))
      | ~ m1_subset_1(A_100,k1_zfmisc_1(A_103))
      | r1_xboole_0(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_223,c_14])).

tff(c_493,plain,(
    ! [A_104,B_105,B_106,A_107] :
      ( r2_hidden('#skF_1'(A_104,B_105),B_106)
      | ~ m1_subset_1(A_104,k1_zfmisc_1(A_107))
      | r1_xboole_0(A_104,B_105)
      | ~ r1_tarski(A_107,B_106) ) ),
    inference(resolution,[status(thm)],[c_18,c_489])).

tff(c_497,plain,(
    ! [A_108,B_109,B_110,B_111] :
      ( r2_hidden('#skF_1'(A_108,B_109),B_110)
      | r1_xboole_0(A_108,B_109)
      | ~ r1_tarski(B_111,B_110)
      | ~ r1_tarski(A_108,B_111) ) ),
    inference(resolution,[status(thm)],[c_18,c_493])).

tff(c_509,plain,(
    ! [A_108,B_109,B_7] :
      ( r2_hidden('#skF_1'(A_108,B_109),B_7)
      | r1_xboole_0(A_108,B_109)
      | ~ r1_tarski(A_108,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_497])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_174,plain,(
    ! [A_70,B_71] :
      ( r1_xboole_0(u1_struct_0(A_70),u1_struct_0(B_71))
      | ~ r1_tsep_1(A_70,B_71)
      | ~ l1_struct_0(B_71)
      | ~ l1_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_382,plain,(
    ! [C_94,B_95,A_96] :
      ( ~ r2_hidden(C_94,u1_struct_0(B_95))
      | ~ r2_hidden(C_94,u1_struct_0(A_96))
      | ~ r1_tsep_1(A_96,B_95)
      | ~ l1_struct_0(B_95)
      | ~ l1_struct_0(A_96) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_530,plain,(
    ! [A_127,B_128,A_129] :
      ( ~ r2_hidden('#skF_1'(A_127,u1_struct_0(B_128)),u1_struct_0(A_129))
      | ~ r1_tsep_1(A_129,B_128)
      | ~ l1_struct_0(B_128)
      | ~ l1_struct_0(A_129)
      | r1_xboole_0(A_127,u1_struct_0(B_128)) ) ),
    inference(resolution,[status(thm)],[c_4,c_382])).

tff(c_615,plain,(
    ! [A_148,B_149,A_150] :
      ( ~ r1_tsep_1(A_148,B_149)
      | ~ l1_struct_0(B_149)
      | ~ l1_struct_0(A_148)
      | r1_xboole_0(A_150,u1_struct_0(B_149))
      | ~ r1_tarski(A_150,u1_struct_0(A_148)) ) ),
    inference(resolution,[status(thm)],[c_509,c_530])).

tff(c_619,plain,(
    ! [A_150] :
      ( ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0('#skF_4')
      | r1_xboole_0(A_150,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_150,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_62,c_615])).

tff(c_672,plain,(
    ! [A_155] :
      ( r1_xboole_0(A_155,u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_155,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_167,c_619])).

tff(c_26,plain,(
    ! [A_21,B_23] :
      ( r1_tsep_1(A_21,B_23)
      | ~ r1_xboole_0(u1_struct_0(A_21),u1_struct_0(B_23))
      | ~ l1_struct_0(B_23)
      | ~ l1_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_676,plain,(
    ! [A_21] :
      ( r1_tsep_1(A_21,'#skF_5')
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0(A_21)
      | ~ r1_tarski(u1_struct_0(A_21),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_672,c_26])).

tff(c_767,plain,(
    ! [A_163] :
      ( r1_tsep_1(A_163,'#skF_5')
      | ~ l1_struct_0(A_163)
      | ~ r1_tarski(u1_struct_0(A_163),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_676])).

tff(c_779,plain,(
    ! [B_164] :
      ( r1_tsep_1(B_164,'#skF_5')
      | ~ l1_struct_0(B_164)
      | ~ m1_pre_topc(B_164,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_302,c_767])).

tff(c_38,plain,
    ( ~ r1_tsep_1('#skF_5','#skF_3')
    | ~ r1_tsep_1('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_63,plain,(
    ~ r1_tsep_1('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_792,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_779,c_63])).

tff(c_807,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_792])).

tff(c_810,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_807])).

tff(c_814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_810])).

tff(c_815,plain,(
    ~ r1_tsep_1('#skF_5','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_816,plain,(
    r1_tsep_1('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_892,plain,(
    ! [B_185,A_186] :
      ( r1_tsep_1(B_185,A_186)
      | ~ r1_tsep_1(A_186,B_185)
      | ~ l1_struct_0(B_185)
      | ~ l1_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_894,plain,
    ( r1_tsep_1('#skF_5','#skF_3')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_816,c_892])).

tff(c_899,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_815,c_894])).

tff(c_902,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_899])).

tff(c_905,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_902])).

tff(c_909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_905])).

tff(c_910,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_899])).

tff(c_915,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_910])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_915])).

tff(c_921,plain,(
    ~ r1_tsep_1('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_920,plain,(
    r1_tsep_1('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1003,plain,(
    ! [B_209,A_210] :
      ( r1_tsep_1(B_209,A_210)
      | ~ r1_tsep_1(A_210,B_209)
      | ~ l1_struct_0(B_209)
      | ~ l1_struct_0(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1005,plain,
    ( r1_tsep_1('#skF_4','#skF_5')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_920,c_1003])).

tff(c_1008,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_921,c_1005])).

tff(c_1009,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1008])).

tff(c_1012,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1009])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_1012])).

tff(c_1017,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1008])).

tff(c_1021,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1017])).

tff(c_1025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_956,c_1021])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.60  
% 3.30/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.60  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.30/1.60  
% 3.30/1.60  %Foreground sorts:
% 3.30/1.60  
% 3.30/1.60  
% 3.30/1.60  %Background operators:
% 3.30/1.60  
% 3.30/1.60  
% 3.30/1.60  %Foreground operators:
% 3.30/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.30/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.30/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.30/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.30/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.30/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.30/1.60  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.30/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.30/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.30/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.60  
% 3.30/1.62  tff(f_149, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.30/1.62  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.30/1.62  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.30/1.62  tff(f_69, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.30/1.62  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.30/1.62  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.30/1.62  tff(f_97, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.30/1.62  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.30/1.62  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.30/1.62  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.30/1.62  tff(f_89, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.30/1.62  tff(c_54, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_929, plain, (![B_193, A_194]: (l1_pre_topc(B_193) | ~m1_pre_topc(B_193, A_194) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.30/1.62  tff(c_941, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_929])).
% 3.30/1.62  tff(c_951, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_941])).
% 3.30/1.62  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_948, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_40, c_929])).
% 3.30/1.62  tff(c_952, plain, (~l1_pre_topc('#skF_4')), inference(splitLeft, [status(thm)], [c_948])).
% 3.30/1.62  tff(c_954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_951, c_952])).
% 3.30/1.62  tff(c_956, plain, (l1_pre_topc('#skF_4')), inference(splitRight, [status(thm)], [c_948])).
% 3.30/1.62  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.30/1.62  tff(c_42, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_932, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_929])).
% 3.30/1.62  tff(c_944, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_932])).
% 3.30/1.62  tff(c_823, plain, (![B_169, A_170]: (l1_pre_topc(B_169) | ~m1_pre_topc(B_169, A_170) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.30/1.62  tff(c_826, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_823])).
% 3.30/1.62  tff(c_838, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_826])).
% 3.30/1.62  tff(c_50, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_829, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_823])).
% 3.30/1.62  tff(c_841, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_829])).
% 3.30/1.62  tff(c_65, plain, (![B_48, A_49]: (l1_pre_topc(B_48) | ~m1_pre_topc(B_48, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.30/1.62  tff(c_71, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_65])).
% 3.30/1.62  tff(c_83, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_71])).
% 3.30/1.62  tff(c_56, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_109, plain, (![B_58, A_59]: (v2_pre_topc(B_58) | ~m1_pre_topc(B_58, A_59) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.30/1.62  tff(c_121, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_109])).
% 3.30/1.62  tff(c_133, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_121])).
% 3.30/1.62  tff(c_77, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_65])).
% 3.30/1.62  tff(c_87, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_77])).
% 3.30/1.62  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.30/1.62  tff(c_227, plain, (![B_85, C_86, A_87]: (m1_pre_topc(B_85, C_86) | ~r1_tarski(u1_struct_0(B_85), u1_struct_0(C_86)) | ~m1_pre_topc(C_86, A_87) | ~m1_pre_topc(B_85, A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.30/1.62  tff(c_244, plain, (![B_88, A_89]: (m1_pre_topc(B_88, B_88) | ~m1_pre_topc(B_88, A_89) | ~l1_pre_topc(A_89) | ~v2_pre_topc(A_89))), inference(resolution, [status(thm)], [c_12, c_227])).
% 3.30/1.62  tff(c_252, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_244])).
% 3.30/1.62  tff(c_264, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_252])).
% 3.30/1.62  tff(c_32, plain, (![B_30, C_32, A_26]: (r1_tarski(u1_struct_0(B_30), u1_struct_0(C_32)) | ~m1_pre_topc(B_30, C_32) | ~m1_pre_topc(C_32, A_26) | ~m1_pre_topc(B_30, A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.30/1.62  tff(c_290, plain, (![B_30]: (r1_tarski(u1_struct_0(B_30), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_30, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_264, c_32])).
% 3.30/1.62  tff(c_302, plain, (![B_30]: (r1_tarski(u1_struct_0(B_30), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_30, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_87, c_290])).
% 3.30/1.62  tff(c_68, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_65])).
% 3.30/1.62  tff(c_80, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68])).
% 3.30/1.62  tff(c_36, plain, (r1_tsep_1('#skF_5', '#skF_4') | r1_tsep_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_62, plain, (r1_tsep_1('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_36])).
% 3.30/1.62  tff(c_144, plain, (![B_66, A_67]: (r1_tsep_1(B_66, A_67) | ~r1_tsep_1(A_67, B_66) | ~l1_struct_0(B_66) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.30/1.62  tff(c_147, plain, (r1_tsep_1('#skF_5', '#skF_4') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_62, c_144])).
% 3.30/1.62  tff(c_148, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_147])).
% 3.30/1.62  tff(c_151, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_148])).
% 3.30/1.62  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_151])).
% 3.30/1.62  tff(c_156, plain, (~l1_struct_0('#skF_5') | r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_147])).
% 3.30/1.62  tff(c_158, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_156])).
% 3.30/1.62  tff(c_161, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_158])).
% 3.30/1.62  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_161])).
% 3.30/1.62  tff(c_167, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_156])).
% 3.30/1.62  tff(c_157, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_147])).
% 3.30/1.62  tff(c_18, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.30/1.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.62  tff(c_137, plain, (![C_63, A_64, B_65]: (r2_hidden(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.30/1.62  tff(c_223, plain, (![A_82, B_83, A_84]: (r2_hidden('#skF_1'(A_82, B_83), A_84) | ~m1_subset_1(A_82, k1_zfmisc_1(A_84)) | r1_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_6, c_137])).
% 3.30/1.62  tff(c_14, plain, (![C_11, A_8, B_9]: (r2_hidden(C_11, A_8) | ~r2_hidden(C_11, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.30/1.62  tff(c_489, plain, (![A_100, B_101, A_102, A_103]: (r2_hidden('#skF_1'(A_100, B_101), A_102) | ~m1_subset_1(A_103, k1_zfmisc_1(A_102)) | ~m1_subset_1(A_100, k1_zfmisc_1(A_103)) | r1_xboole_0(A_100, B_101))), inference(resolution, [status(thm)], [c_223, c_14])).
% 3.30/1.62  tff(c_493, plain, (![A_104, B_105, B_106, A_107]: (r2_hidden('#skF_1'(A_104, B_105), B_106) | ~m1_subset_1(A_104, k1_zfmisc_1(A_107)) | r1_xboole_0(A_104, B_105) | ~r1_tarski(A_107, B_106))), inference(resolution, [status(thm)], [c_18, c_489])).
% 3.30/1.62  tff(c_497, plain, (![A_108, B_109, B_110, B_111]: (r2_hidden('#skF_1'(A_108, B_109), B_110) | r1_xboole_0(A_108, B_109) | ~r1_tarski(B_111, B_110) | ~r1_tarski(A_108, B_111))), inference(resolution, [status(thm)], [c_18, c_493])).
% 3.30/1.62  tff(c_509, plain, (![A_108, B_109, B_7]: (r2_hidden('#skF_1'(A_108, B_109), B_7) | r1_xboole_0(A_108, B_109) | ~r1_tarski(A_108, B_7))), inference(resolution, [status(thm)], [c_12, c_497])).
% 3.30/1.62  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.62  tff(c_174, plain, (![A_70, B_71]: (r1_xboole_0(u1_struct_0(A_70), u1_struct_0(B_71)) | ~r1_tsep_1(A_70, B_71) | ~l1_struct_0(B_71) | ~l1_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.30/1.62  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.30/1.62  tff(c_382, plain, (![C_94, B_95, A_96]: (~r2_hidden(C_94, u1_struct_0(B_95)) | ~r2_hidden(C_94, u1_struct_0(A_96)) | ~r1_tsep_1(A_96, B_95) | ~l1_struct_0(B_95) | ~l1_struct_0(A_96))), inference(resolution, [status(thm)], [c_174, c_2])).
% 3.30/1.62  tff(c_530, plain, (![A_127, B_128, A_129]: (~r2_hidden('#skF_1'(A_127, u1_struct_0(B_128)), u1_struct_0(A_129)) | ~r1_tsep_1(A_129, B_128) | ~l1_struct_0(B_128) | ~l1_struct_0(A_129) | r1_xboole_0(A_127, u1_struct_0(B_128)))), inference(resolution, [status(thm)], [c_4, c_382])).
% 3.30/1.62  tff(c_615, plain, (![A_148, B_149, A_150]: (~r1_tsep_1(A_148, B_149) | ~l1_struct_0(B_149) | ~l1_struct_0(A_148) | r1_xboole_0(A_150, u1_struct_0(B_149)) | ~r1_tarski(A_150, u1_struct_0(A_148)))), inference(resolution, [status(thm)], [c_509, c_530])).
% 3.30/1.62  tff(c_619, plain, (![A_150]: (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_4') | r1_xboole_0(A_150, u1_struct_0('#skF_5')) | ~r1_tarski(A_150, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_62, c_615])).
% 3.30/1.62  tff(c_672, plain, (![A_155]: (r1_xboole_0(A_155, u1_struct_0('#skF_5')) | ~r1_tarski(A_155, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_167, c_619])).
% 3.30/1.62  tff(c_26, plain, (![A_21, B_23]: (r1_tsep_1(A_21, B_23) | ~r1_xboole_0(u1_struct_0(A_21), u1_struct_0(B_23)) | ~l1_struct_0(B_23) | ~l1_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.30/1.62  tff(c_676, plain, (![A_21]: (r1_tsep_1(A_21, '#skF_5') | ~l1_struct_0('#skF_5') | ~l1_struct_0(A_21) | ~r1_tarski(u1_struct_0(A_21), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_672, c_26])).
% 3.30/1.62  tff(c_767, plain, (![A_163]: (r1_tsep_1(A_163, '#skF_5') | ~l1_struct_0(A_163) | ~r1_tarski(u1_struct_0(A_163), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_676])).
% 3.30/1.62  tff(c_779, plain, (![B_164]: (r1_tsep_1(B_164, '#skF_5') | ~l1_struct_0(B_164) | ~m1_pre_topc(B_164, '#skF_4'))), inference(resolution, [status(thm)], [c_302, c_767])).
% 3.30/1.62  tff(c_38, plain, (~r1_tsep_1('#skF_5', '#skF_3') | ~r1_tsep_1('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.30/1.62  tff(c_63, plain, (~r1_tsep_1('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 3.30/1.62  tff(c_792, plain, (~l1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_779, c_63])).
% 3.30/1.62  tff(c_807, plain, (~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_792])).
% 3.30/1.62  tff(c_810, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_807])).
% 3.30/1.62  tff(c_814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_810])).
% 3.30/1.62  tff(c_815, plain, (~r1_tsep_1('#skF_5', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.30/1.62  tff(c_816, plain, (r1_tsep_1('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 3.30/1.62  tff(c_892, plain, (![B_185, A_186]: (r1_tsep_1(B_185, A_186) | ~r1_tsep_1(A_186, B_185) | ~l1_struct_0(B_185) | ~l1_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.30/1.62  tff(c_894, plain, (r1_tsep_1('#skF_5', '#skF_3') | ~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_816, c_892])).
% 3.30/1.62  tff(c_899, plain, (~l1_struct_0('#skF_5') | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_815, c_894])).
% 3.30/1.62  tff(c_902, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_899])).
% 3.30/1.62  tff(c_905, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_902])).
% 3.30/1.62  tff(c_909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_841, c_905])).
% 3.30/1.62  tff(c_910, plain, (~l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_899])).
% 3.30/1.62  tff(c_915, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_910])).
% 3.30/1.62  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_838, c_915])).
% 3.30/1.62  tff(c_921, plain, (~r1_tsep_1('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 3.30/1.62  tff(c_920, plain, (r1_tsep_1('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 3.30/1.62  tff(c_1003, plain, (![B_209, A_210]: (r1_tsep_1(B_209, A_210) | ~r1_tsep_1(A_210, B_209) | ~l1_struct_0(B_209) | ~l1_struct_0(A_210))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.30/1.62  tff(c_1005, plain, (r1_tsep_1('#skF_4', '#skF_5') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_920, c_1003])).
% 3.30/1.62  tff(c_1008, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_921, c_1005])).
% 3.30/1.62  tff(c_1009, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1008])).
% 3.30/1.62  tff(c_1012, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1009])).
% 3.30/1.62  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_944, c_1012])).
% 3.30/1.62  tff(c_1017, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1008])).
% 3.30/1.62  tff(c_1021, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1017])).
% 3.30/1.62  tff(c_1025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_956, c_1021])).
% 3.30/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.62  
% 3.30/1.62  Inference rules
% 3.30/1.62  ----------------------
% 3.30/1.62  #Ref     : 0
% 3.30/1.62  #Sup     : 174
% 3.30/1.62  #Fact    : 0
% 3.30/1.62  #Define  : 0
% 3.30/1.62  #Split   : 13
% 3.30/1.62  #Chain   : 0
% 3.30/1.62  #Close   : 0
% 3.30/1.62  
% 3.30/1.62  Ordering : KBO
% 3.30/1.62  
% 3.30/1.62  Simplification rules
% 3.30/1.62  ----------------------
% 3.30/1.62  #Subsume      : 23
% 3.30/1.62  #Demod        : 144
% 3.30/1.62  #Tautology    : 44
% 3.30/1.62  #SimpNegUnit  : 2
% 3.30/1.62  #BackRed      : 0
% 3.30/1.62  
% 3.30/1.62  #Partial instantiations: 0
% 3.30/1.62  #Strategies tried      : 1
% 3.30/1.62  
% 3.30/1.62  Timing (in seconds)
% 3.30/1.62  ----------------------
% 3.30/1.63  Preprocessing        : 0.38
% 3.30/1.63  Parsing              : 0.22
% 3.30/1.63  CNF conversion       : 0.03
% 3.30/1.63  Main loop            : 0.41
% 3.30/1.63  Inferencing          : 0.16
% 3.30/1.63  Reduction            : 0.11
% 3.30/1.63  Demodulation         : 0.07
% 3.30/1.63  BG Simplification    : 0.02
% 3.30/1.63  Subsumption          : 0.09
% 3.30/1.63  Abstraction          : 0.02
% 3.30/1.63  MUC search           : 0.00
% 3.30/1.63  Cooper               : 0.00
% 3.30/1.63  Total                : 0.84
% 3.30/1.63  Index Insertion      : 0.00
% 3.30/1.63  Index Deletion       : 0.00
% 3.30/1.63  Index Matching       : 0.00
% 3.30/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------

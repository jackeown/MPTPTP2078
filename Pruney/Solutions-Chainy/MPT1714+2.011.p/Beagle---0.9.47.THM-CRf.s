%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:34 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 652 expanded)
%              Number of leaves         :   41 ( 225 expanded)
%              Depth                    :   14
%              Number of atoms          :  293 (2233 expanded)
%              Number of equality atoms :   17 ( 113 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(B,A)
          <=> ( r1_tarski(k2_struct_0(B),k2_struct_0(A))
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
                 => ( r2_hidden(C,u1_pre_topc(B))
                  <=> ? [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                        & r2_hidden(D,u1_pre_topc(A))
                        & C = k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

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

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_94,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_82,plain,(
    m1_pre_topc('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2440,plain,(
    ! [B_230,A_231] :
      ( l1_pre_topc(B_230)
      | ~ m1_pre_topc(B_230,A_231)
      | ~ l1_pre_topc(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2443,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_2440])).

tff(c_2455,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2443])).

tff(c_66,plain,(
    ! [A_60] :
      ( l1_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_90,plain,(
    m1_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2446,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_2440])).

tff(c_2458,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2446])).

tff(c_86,plain,(
    m1_pre_topc('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_2331,plain,(
    ! [B_209,A_210] :
      ( l1_pre_topc(B_209)
      | ~ m1_pre_topc(B_209,A_210)
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2343,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_2331])).

tff(c_2353,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2343])).

tff(c_2334,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_2331])).

tff(c_2346,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2334])).

tff(c_78,plain,
    ( ~ r1_tsep_1('#skF_10','#skF_8')
    | ~ r1_tsep_1('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_103,plain,(
    ~ r1_tsep_1('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_119,plain,(
    ! [B_86,A_87] :
      ( l1_pre_topc(B_86)
      | ~ m1_pre_topc(B_86,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_10')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_82,c_119])).

tff(c_134,plain,(
    l1_pre_topc('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_122])).

tff(c_131,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_119])).

tff(c_141,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_131])).

tff(c_76,plain,
    ( r1_tsep_1('#skF_10','#skF_9')
    | r1_tsep_1('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_109,plain,(
    r1_tsep_1('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_184,plain,(
    ! [B_105,A_106] :
      ( r1_tsep_1(B_105,A_106)
      | ~ r1_tsep_1(A_106,B_105)
      | ~ l1_struct_0(B_105)
      | ~ l1_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_187,plain,
    ( r1_tsep_1('#skF_10','#skF_9')
    | ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_109,c_184])).

tff(c_188,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_191,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_66,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_191])).

tff(c_196,plain,
    ( ~ l1_struct_0('#skF_10')
    | r1_tsep_1('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_203,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_206,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_203])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_206])).

tff(c_212,plain,(
    l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_125,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_90,c_119])).

tff(c_137,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_125])).

tff(c_104,plain,(
    ! [A_84] :
      ( u1_struct_0(A_84) = k2_struct_0(A_84)
      | ~ l1_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_108,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = k2_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_66,c_104])).

tff(c_149,plain,(
    u1_struct_0('#skF_8') = k2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_137,c_108])).

tff(c_110,plain,(
    ! [A_85] :
      ( u1_struct_0(A_85) = k2_struct_0(A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_66,c_104])).

tff(c_114,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_94,c_110])).

tff(c_338,plain,(
    ! [A_118,B_119] :
      ( r1_xboole_0(u1_struct_0(A_118),u1_struct_0(B_119))
      | ~ r1_tsep_1(A_118,B_119)
      | ~ l1_struct_0(B_119)
      | ~ l1_struct_0(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_361,plain,(
    ! [B_119] :
      ( r1_xboole_0(k2_struct_0('#skF_7'),u1_struct_0(B_119))
      | ~ r1_tsep_1('#skF_7',B_119)
      | ~ l1_struct_0(B_119)
      | ~ l1_struct_0('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_338])).

tff(c_374,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_361])).

tff(c_377,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_374])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_377])).

tff(c_383,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_361])).

tff(c_415,plain,(
    ! [A_121,B_122] :
      ( r1_tsep_1(A_121,B_122)
      | ~ r1_xboole_0(u1_struct_0(A_121),u1_struct_0(B_122))
      | ~ l1_struct_0(B_122)
      | ~ l1_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_442,plain,(
    ! [A_121] :
      ( r1_tsep_1(A_121,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_121),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_121) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_415])).

tff(c_523,plain,(
    ! [A_128] :
      ( r1_tsep_1(A_128,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_128),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_442])).

tff(c_532,plain,
    ( r1_tsep_1('#skF_8','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_8'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_523])).

tff(c_588,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_532])).

tff(c_591,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_588])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_591])).

tff(c_597,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_80,plain,(
    m1_pre_topc('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_56,plain,(
    ! [B_42,A_20] :
      ( r1_tarski(k2_struct_0(B_42),k2_struct_0(A_20))
      | ~ m1_pre_topc(B_42,A_20)
      | ~ l1_pre_topc(B_42)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_223,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_tarski(k2_xboole_0(A_107,C_108),B_109)
      | ~ r1_tarski(C_108,B_109)
      | ~ r1_tarski(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_171,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_176,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(k2_xboole_0(A_14,B_15),A_14) ) ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_227,plain,(
    ! [B_109,C_108] :
      ( k2_xboole_0(B_109,C_108) = B_109
      | ~ r1_tarski(C_108,B_109)
      | ~ r1_tarski(B_109,B_109) ) ),
    inference(resolution,[status(thm)],[c_223,c_176])).

tff(c_234,plain,(
    ! [B_110,C_111] :
      ( k2_xboole_0(B_110,C_111) = B_110
      | ~ r1_tarski(C_111,B_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_227])).

tff(c_246,plain,(
    ! [B_13] : k2_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_234])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(k2_xboole_0(A_16,C_18),B_17)
      | ~ r1_tarski(C_18,B_17)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_938,plain,(
    ! [B_154,A_155,C_156] :
      ( k2_xboole_0(B_154,k2_xboole_0(A_155,C_156)) = B_154
      | ~ r1_tarski(C_156,B_154)
      | ~ r1_tarski(A_155,B_154) ) ),
    inference(resolution,[status(thm)],[c_34,c_234])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2046,plain,(
    ! [D_191,A_192,C_193,B_194] :
      ( ~ r2_hidden(D_191,k2_xboole_0(A_192,C_193))
      | r2_hidden(D_191,B_194)
      | ~ r1_tarski(C_193,B_194)
      | ~ r1_tarski(A_192,B_194) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_938,c_4])).

tff(c_2110,plain,(
    ! [D_198,B_199,B_200] :
      ( ~ r2_hidden(D_198,B_199)
      | r2_hidden(D_198,B_200)
      | ~ r1_tarski(B_199,B_200)
      | ~ r1_tarski(B_199,B_200) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_2046])).

tff(c_2156,plain,(
    ! [A_201,B_202,B_203] :
      ( r2_hidden('#skF_3'(A_201,B_202),B_203)
      | ~ r1_tarski(B_202,B_203)
      | r1_xboole_0(A_201,B_202) ) ),
    inference(resolution,[status(thm)],[c_22,c_2110])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_145,plain,(
    u1_struct_0('#skF_10') = k2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_134,c_108])).

tff(c_197,plain,(
    l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_153,plain,(
    u1_struct_0('#skF_9') = k2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_141,c_108])).

tff(c_343,plain,(
    ! [B_119] :
      ( r1_xboole_0(k2_struct_0('#skF_9'),u1_struct_0(B_119))
      | ~ r1_tsep_1('#skF_9',B_119)
      | ~ l1_struct_0(B_119)
      | ~ l1_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_338])).

tff(c_389,plain,(
    ! [B_120] :
      ( r1_xboole_0(k2_struct_0('#skF_9'),u1_struct_0(B_120))
      | ~ r1_tsep_1('#skF_9',B_120)
      | ~ l1_struct_0(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_343])).

tff(c_400,plain,
    ( r1_xboole_0(k2_struct_0('#skF_9'),k2_struct_0('#skF_10'))
    | ~ r1_tsep_1('#skF_9','#skF_10')
    | ~ l1_struct_0('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_389])).

tff(c_408,plain,(
    r1_xboole_0(k2_struct_0('#skF_9'),k2_struct_0('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_109,c_400])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_483,plain,(
    ! [C_124] :
      ( ~ r2_hidden(C_124,k2_struct_0('#skF_10'))
      | ~ r2_hidden(C_124,k2_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_408,c_20])).

tff(c_493,plain,(
    ! [B_8] :
      ( ~ r2_hidden('#skF_3'(k2_struct_0('#skF_10'),B_8),k2_struct_0('#skF_9'))
      | r1_xboole_0(k2_struct_0('#skF_10'),B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_483])).

tff(c_2229,plain,(
    ! [B_204] :
      ( ~ r1_tarski(B_204,k2_struct_0('#skF_9'))
      | r1_xboole_0(k2_struct_0('#skF_10'),B_204) ) ),
    inference(resolution,[status(thm)],[c_2156,c_493])).

tff(c_355,plain,(
    ! [B_119] :
      ( r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_119))
      | ~ r1_tsep_1('#skF_10',B_119)
      | ~ l1_struct_0(B_119)
      | ~ l1_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_338])).

tff(c_710,plain,(
    ! [B_142] :
      ( r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_142))
      | ~ r1_tsep_1('#skF_10',B_142)
      | ~ l1_struct_0(B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_355])).

tff(c_718,plain,
    ( r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8'))
    | ~ r1_tsep_1('#skF_10','#skF_8')
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_710])).

tff(c_729,plain,
    ( r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8'))
    | ~ r1_tsep_1('#skF_10','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_718])).

tff(c_738,plain,(
    ~ r1_tsep_1('#skF_10','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_729])).

tff(c_433,plain,(
    ! [B_122] :
      ( r1_tsep_1('#skF_10',B_122)
      | ~ r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_122))
      | ~ l1_struct_0(B_122)
      | ~ l1_struct_0('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_415])).

tff(c_739,plain,(
    ! [B_143] :
      ( r1_tsep_1('#skF_10',B_143)
      | ~ r1_xboole_0(k2_struct_0('#skF_10'),u1_struct_0(B_143))
      | ~ l1_struct_0(B_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_433])).

tff(c_748,plain,
    ( r1_tsep_1('#skF_10','#skF_8')
    | ~ r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8'))
    | ~ l1_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_739])).

tff(c_759,plain,
    ( r1_tsep_1('#skF_10','#skF_8')
    | ~ r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_748])).

tff(c_760,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_10'),k2_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_738,c_759])).

tff(c_2245,plain,(
    ~ r1_tarski(k2_struct_0('#skF_8'),k2_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_2229,c_760])).

tff(c_2294,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_2245])).

tff(c_2298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_137,c_80,c_2294])).

tff(c_2300,plain,(
    r1_tsep_1('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_729])).

tff(c_74,plain,(
    ! [B_68,A_67] :
      ( r1_tsep_1(B_68,A_67)
      | ~ r1_tsep_1(A_67,B_68)
      | ~ l1_struct_0(B_68)
      | ~ l1_struct_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2323,plain,
    ( r1_tsep_1('#skF_8','#skF_10')
    | ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2300,c_74])).

tff(c_2326,plain,(
    r1_tsep_1('#skF_8','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_597,c_2323])).

tff(c_2328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_2326])).

tff(c_2330,plain,(
    ~ r1_tsep_1('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2329,plain,(
    r1_tsep_1('#skF_10','#skF_9') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2404,plain,(
    ! [B_227,A_228] :
      ( r1_tsep_1(B_227,A_228)
      | ~ r1_tsep_1(A_228,B_227)
      | ~ l1_struct_0(B_227)
      | ~ l1_struct_0(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2406,plain,
    ( r1_tsep_1('#skF_9','#skF_10')
    | ~ l1_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_2329,c_2404])).

tff(c_2409,plain,
    ( ~ l1_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_2330,c_2406])).

tff(c_2410,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2409])).

tff(c_2413,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_2410])).

tff(c_2417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2346,c_2413])).

tff(c_2418,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2409])).

tff(c_2427,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_66,c_2418])).

tff(c_2431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2353,c_2427])).

tff(c_2432,plain,(
    ~ r1_tsep_1('#skF_10','#skF_8') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2433,plain,(
    r1_tsep_1('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_2514,plain,(
    ! [B_250,A_251] :
      ( r1_tsep_1(B_250,A_251)
      | ~ r1_tsep_1(A_251,B_250)
      | ~ l1_struct_0(B_250)
      | ~ l1_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2518,plain,
    ( r1_tsep_1('#skF_10','#skF_8')
    | ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_2433,c_2514])).

tff(c_2522,plain,
    ( ~ l1_struct_0('#skF_10')
    | ~ l1_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_2432,c_2518])).

tff(c_2523,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2522])).

tff(c_2526,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_2523])).

tff(c_2530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2458,c_2526])).

tff(c_2531,plain,(
    ~ l1_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_2522])).

tff(c_2554,plain,(
    ~ l1_pre_topc('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_2531])).

tff(c_2558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_2554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:14:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.88  
% 4.63/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.89  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5
% 4.63/1.89  
% 4.63/1.89  %Foreground sorts:
% 4.63/1.89  
% 4.63/1.89  
% 4.63/1.89  %Background operators:
% 4.63/1.89  
% 4.63/1.89  
% 4.63/1.89  %Foreground operators:
% 4.63/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.63/1.89  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.63/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.63/1.89  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.63/1.89  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.63/1.89  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.63/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.89  tff('#skF_10', type, '#skF_10': $i).
% 4.63/1.89  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.63/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_9', type, '#skF_9': $i).
% 4.63/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.89  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.63/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.63/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.63/1.89  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.63/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.63/1.89  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.63/1.89  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.63/1.89  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.63/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.89  
% 4.63/1.91  tff(f_157, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 4.63/1.91  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.63/1.91  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.63/1.91  tff(f_119, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 4.63/1.91  tff(f_70, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.63/1.91  tff(f_111, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 4.63/1.91  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 4.63/1.91  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.63/1.91  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.63/1.91  tff(f_66, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.63/1.91  tff(f_60, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.63/1.91  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 4.63/1.91  tff(c_94, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.63/1.91  tff(c_82, plain, (m1_pre_topc('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.63/1.91  tff(c_2440, plain, (![B_230, A_231]: (l1_pre_topc(B_230) | ~m1_pre_topc(B_230, A_231) | ~l1_pre_topc(A_231))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.63/1.91  tff(c_2443, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_82, c_2440])).
% 4.63/1.91  tff(c_2455, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2443])).
% 4.63/1.91  tff(c_66, plain, (![A_60]: (l1_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.63/1.91  tff(c_90, plain, (m1_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.63/1.91  tff(c_2446, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_90, c_2440])).
% 4.63/1.91  tff(c_2458, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2446])).
% 4.63/1.91  tff(c_86, plain, (m1_pre_topc('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.63/1.91  tff(c_2331, plain, (![B_209, A_210]: (l1_pre_topc(B_209) | ~m1_pre_topc(B_209, A_210) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.63/1.91  tff(c_2343, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_86, c_2331])).
% 4.63/1.91  tff(c_2353, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2343])).
% 4.63/1.91  tff(c_2334, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_82, c_2331])).
% 4.63/1.91  tff(c_2346, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2334])).
% 4.63/1.91  tff(c_78, plain, (~r1_tsep_1('#skF_10', '#skF_8') | ~r1_tsep_1('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.63/1.91  tff(c_103, plain, (~r1_tsep_1('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_78])).
% 4.63/1.91  tff(c_119, plain, (![B_86, A_87]: (l1_pre_topc(B_86) | ~m1_pre_topc(B_86, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.63/1.91  tff(c_122, plain, (l1_pre_topc('#skF_10') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_82, c_119])).
% 4.63/1.91  tff(c_134, plain, (l1_pre_topc('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_122])).
% 4.63/1.91  tff(c_131, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_86, c_119])).
% 4.63/1.91  tff(c_141, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_131])).
% 4.63/1.91  tff(c_76, plain, (r1_tsep_1('#skF_10', '#skF_9') | r1_tsep_1('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.63/1.91  tff(c_109, plain, (r1_tsep_1('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_76])).
% 4.63/1.91  tff(c_184, plain, (![B_105, A_106]: (r1_tsep_1(B_105, A_106) | ~r1_tsep_1(A_106, B_105) | ~l1_struct_0(B_105) | ~l1_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.63/1.91  tff(c_187, plain, (r1_tsep_1('#skF_10', '#skF_9') | ~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_109, c_184])).
% 4.63/1.91  tff(c_188, plain, (~l1_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_187])).
% 4.63/1.91  tff(c_191, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_66, c_188])).
% 4.63/1.91  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_191])).
% 4.63/1.91  tff(c_196, plain, (~l1_struct_0('#skF_10') | r1_tsep_1('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_187])).
% 4.63/1.91  tff(c_203, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_196])).
% 4.63/1.91  tff(c_206, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_66, c_203])).
% 4.63/1.91  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_206])).
% 4.63/1.91  tff(c_212, plain, (l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_196])).
% 4.63/1.91  tff(c_125, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_90, c_119])).
% 4.63/1.91  tff(c_137, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_125])).
% 4.63/1.91  tff(c_104, plain, (![A_84]: (u1_struct_0(A_84)=k2_struct_0(A_84) | ~l1_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.63/1.91  tff(c_108, plain, (![A_60]: (u1_struct_0(A_60)=k2_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_66, c_104])).
% 4.63/1.91  tff(c_149, plain, (u1_struct_0('#skF_8')=k2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_137, c_108])).
% 4.63/1.91  tff(c_110, plain, (![A_85]: (u1_struct_0(A_85)=k2_struct_0(A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_66, c_104])).
% 4.63/1.91  tff(c_114, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_94, c_110])).
% 4.63/1.91  tff(c_338, plain, (![A_118, B_119]: (r1_xboole_0(u1_struct_0(A_118), u1_struct_0(B_119)) | ~r1_tsep_1(A_118, B_119) | ~l1_struct_0(B_119) | ~l1_struct_0(A_118))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.63/1.91  tff(c_361, plain, (![B_119]: (r1_xboole_0(k2_struct_0('#skF_7'), u1_struct_0(B_119)) | ~r1_tsep_1('#skF_7', B_119) | ~l1_struct_0(B_119) | ~l1_struct_0('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_114, c_338])).
% 4.63/1.91  tff(c_374, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_361])).
% 4.63/1.91  tff(c_377, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_66, c_374])).
% 4.63/1.91  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_377])).
% 4.63/1.91  tff(c_383, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_361])).
% 4.63/1.91  tff(c_415, plain, (![A_121, B_122]: (r1_tsep_1(A_121, B_122) | ~r1_xboole_0(u1_struct_0(A_121), u1_struct_0(B_122)) | ~l1_struct_0(B_122) | ~l1_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.63/1.91  tff(c_442, plain, (![A_121]: (r1_tsep_1(A_121, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_121), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_121))), inference(superposition, [status(thm), theory('equality')], [c_114, c_415])).
% 4.63/1.91  tff(c_523, plain, (![A_128]: (r1_tsep_1(A_128, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_128), k2_struct_0('#skF_7')) | ~l1_struct_0(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_442])).
% 4.63/1.91  tff(c_532, plain, (r1_tsep_1('#skF_8', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_8'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_149, c_523])).
% 4.63/1.91  tff(c_588, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_532])).
% 4.63/1.91  tff(c_591, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_66, c_588])).
% 4.63/1.91  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_591])).
% 4.63/1.91  tff(c_597, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_532])).
% 4.63/1.91  tff(c_80, plain, (m1_pre_topc('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.63/1.91  tff(c_56, plain, (![B_42, A_20]: (r1_tarski(k2_struct_0(B_42), k2_struct_0(A_20)) | ~m1_pre_topc(B_42, A_20) | ~l1_pre_topc(B_42) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.63/1.91  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.91  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.91  tff(c_223, plain, (![A_107, C_108, B_109]: (r1_tarski(k2_xboole_0(A_107, C_108), B_109) | ~r1_tarski(C_108, B_109) | ~r1_tarski(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.63/1.91  tff(c_32, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.63/1.91  tff(c_171, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.63/1.91  tff(c_176, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(k2_xboole_0(A_14, B_15), A_14))), inference(resolution, [status(thm)], [c_32, c_171])).
% 4.63/1.91  tff(c_227, plain, (![B_109, C_108]: (k2_xboole_0(B_109, C_108)=B_109 | ~r1_tarski(C_108, B_109) | ~r1_tarski(B_109, B_109))), inference(resolution, [status(thm)], [c_223, c_176])).
% 4.63/1.91  tff(c_234, plain, (![B_110, C_111]: (k2_xboole_0(B_110, C_111)=B_110 | ~r1_tarski(C_111, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_227])).
% 4.63/1.91  tff(c_246, plain, (![B_13]: (k2_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_234])).
% 4.63/1.91  tff(c_34, plain, (![A_16, C_18, B_17]: (r1_tarski(k2_xboole_0(A_16, C_18), B_17) | ~r1_tarski(C_18, B_17) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.63/1.91  tff(c_938, plain, (![B_154, A_155, C_156]: (k2_xboole_0(B_154, k2_xboole_0(A_155, C_156))=B_154 | ~r1_tarski(C_156, B_154) | ~r1_tarski(A_155, B_154))), inference(resolution, [status(thm)], [c_34, c_234])).
% 4.63/1.91  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.63/1.91  tff(c_2046, plain, (![D_191, A_192, C_193, B_194]: (~r2_hidden(D_191, k2_xboole_0(A_192, C_193)) | r2_hidden(D_191, B_194) | ~r1_tarski(C_193, B_194) | ~r1_tarski(A_192, B_194))), inference(superposition, [status(thm), theory('equality')], [c_938, c_4])).
% 4.63/1.91  tff(c_2110, plain, (![D_198, B_199, B_200]: (~r2_hidden(D_198, B_199) | r2_hidden(D_198, B_200) | ~r1_tarski(B_199, B_200) | ~r1_tarski(B_199, B_200))), inference(superposition, [status(thm), theory('equality')], [c_246, c_2046])).
% 4.63/1.91  tff(c_2156, plain, (![A_201, B_202, B_203]: (r2_hidden('#skF_3'(A_201, B_202), B_203) | ~r1_tarski(B_202, B_203) | r1_xboole_0(A_201, B_202))), inference(resolution, [status(thm)], [c_22, c_2110])).
% 4.63/1.91  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.91  tff(c_145, plain, (u1_struct_0('#skF_10')=k2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_134, c_108])).
% 4.63/1.91  tff(c_197, plain, (l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_187])).
% 4.63/1.91  tff(c_153, plain, (u1_struct_0('#skF_9')=k2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_141, c_108])).
% 4.63/1.91  tff(c_343, plain, (![B_119]: (r1_xboole_0(k2_struct_0('#skF_9'), u1_struct_0(B_119)) | ~r1_tsep_1('#skF_9', B_119) | ~l1_struct_0(B_119) | ~l1_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_338])).
% 4.63/1.91  tff(c_389, plain, (![B_120]: (r1_xboole_0(k2_struct_0('#skF_9'), u1_struct_0(B_120)) | ~r1_tsep_1('#skF_9', B_120) | ~l1_struct_0(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_343])).
% 4.63/1.91  tff(c_400, plain, (r1_xboole_0(k2_struct_0('#skF_9'), k2_struct_0('#skF_10')) | ~r1_tsep_1('#skF_9', '#skF_10') | ~l1_struct_0('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_145, c_389])).
% 4.63/1.91  tff(c_408, plain, (r1_xboole_0(k2_struct_0('#skF_9'), k2_struct_0('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_109, c_400])).
% 4.63/1.91  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.63/1.91  tff(c_483, plain, (![C_124]: (~r2_hidden(C_124, k2_struct_0('#skF_10')) | ~r2_hidden(C_124, k2_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_408, c_20])).
% 4.63/1.91  tff(c_493, plain, (![B_8]: (~r2_hidden('#skF_3'(k2_struct_0('#skF_10'), B_8), k2_struct_0('#skF_9')) | r1_xboole_0(k2_struct_0('#skF_10'), B_8))), inference(resolution, [status(thm)], [c_24, c_483])).
% 4.63/1.91  tff(c_2229, plain, (![B_204]: (~r1_tarski(B_204, k2_struct_0('#skF_9')) | r1_xboole_0(k2_struct_0('#skF_10'), B_204))), inference(resolution, [status(thm)], [c_2156, c_493])).
% 4.63/1.91  tff(c_355, plain, (![B_119]: (r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_119)) | ~r1_tsep_1('#skF_10', B_119) | ~l1_struct_0(B_119) | ~l1_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_338])).
% 4.63/1.91  tff(c_710, plain, (![B_142]: (r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_142)) | ~r1_tsep_1('#skF_10', B_142) | ~l1_struct_0(B_142))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_355])).
% 4.63/1.91  tff(c_718, plain, (r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8')) | ~r1_tsep_1('#skF_10', '#skF_8') | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_149, c_710])).
% 4.63/1.91  tff(c_729, plain, (r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8')) | ~r1_tsep_1('#skF_10', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_597, c_718])).
% 4.63/1.91  tff(c_738, plain, (~r1_tsep_1('#skF_10', '#skF_8')), inference(splitLeft, [status(thm)], [c_729])).
% 4.63/1.91  tff(c_433, plain, (![B_122]: (r1_tsep_1('#skF_10', B_122) | ~r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_122)) | ~l1_struct_0(B_122) | ~l1_struct_0('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_145, c_415])).
% 4.63/1.91  tff(c_739, plain, (![B_143]: (r1_tsep_1('#skF_10', B_143) | ~r1_xboole_0(k2_struct_0('#skF_10'), u1_struct_0(B_143)) | ~l1_struct_0(B_143))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_433])).
% 4.63/1.91  tff(c_748, plain, (r1_tsep_1('#skF_10', '#skF_8') | ~r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8')) | ~l1_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_149, c_739])).
% 4.63/1.91  tff(c_759, plain, (r1_tsep_1('#skF_10', '#skF_8') | ~r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_748])).
% 4.63/1.91  tff(c_760, plain, (~r1_xboole_0(k2_struct_0('#skF_10'), k2_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_738, c_759])).
% 4.63/1.91  tff(c_2245, plain, (~r1_tarski(k2_struct_0('#skF_8'), k2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_2229, c_760])).
% 4.63/1.91  tff(c_2294, plain, (~m1_pre_topc('#skF_8', '#skF_9') | ~l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_56, c_2245])).
% 4.63/1.91  tff(c_2298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_137, c_80, c_2294])).
% 4.63/1.91  tff(c_2300, plain, (r1_tsep_1('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_729])).
% 4.63/1.91  tff(c_74, plain, (![B_68, A_67]: (r1_tsep_1(B_68, A_67) | ~r1_tsep_1(A_67, B_68) | ~l1_struct_0(B_68) | ~l1_struct_0(A_67))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.63/1.91  tff(c_2323, plain, (r1_tsep_1('#skF_8', '#skF_10') | ~l1_struct_0('#skF_8') | ~l1_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2300, c_74])).
% 4.63/1.91  tff(c_2326, plain, (r1_tsep_1('#skF_8', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_212, c_597, c_2323])).
% 4.63/1.91  tff(c_2328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_2326])).
% 4.63/1.91  tff(c_2330, plain, (~r1_tsep_1('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_76])).
% 4.63/1.91  tff(c_2329, plain, (r1_tsep_1('#skF_10', '#skF_9')), inference(splitRight, [status(thm)], [c_76])).
% 4.63/1.91  tff(c_2404, plain, (![B_227, A_228]: (r1_tsep_1(B_227, A_228) | ~r1_tsep_1(A_228, B_227) | ~l1_struct_0(B_227) | ~l1_struct_0(A_228))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.63/1.91  tff(c_2406, plain, (r1_tsep_1('#skF_9', '#skF_10') | ~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_2329, c_2404])).
% 4.63/1.91  tff(c_2409, plain, (~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_2330, c_2406])).
% 4.63/1.91  tff(c_2410, plain, (~l1_struct_0('#skF_10')), inference(splitLeft, [status(thm)], [c_2409])).
% 4.63/1.91  tff(c_2413, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_66, c_2410])).
% 4.63/1.91  tff(c_2417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2346, c_2413])).
% 4.63/1.91  tff(c_2418, plain, (~l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_2409])).
% 4.63/1.91  tff(c_2427, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_66, c_2418])).
% 4.63/1.91  tff(c_2431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2353, c_2427])).
% 4.63/1.91  tff(c_2432, plain, (~r1_tsep_1('#skF_10', '#skF_8')), inference(splitRight, [status(thm)], [c_78])).
% 4.63/1.91  tff(c_2433, plain, (r1_tsep_1('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_78])).
% 4.63/1.91  tff(c_2514, plain, (![B_250, A_251]: (r1_tsep_1(B_250, A_251) | ~r1_tsep_1(A_251, B_250) | ~l1_struct_0(B_250) | ~l1_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.63/1.91  tff(c_2518, plain, (r1_tsep_1('#skF_10', '#skF_8') | ~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_2433, c_2514])).
% 4.63/1.91  tff(c_2522, plain, (~l1_struct_0('#skF_10') | ~l1_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_2432, c_2518])).
% 4.63/1.91  tff(c_2523, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_2522])).
% 4.63/1.91  tff(c_2526, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_66, c_2523])).
% 4.63/1.91  tff(c_2530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2458, c_2526])).
% 4.63/1.91  tff(c_2531, plain, (~l1_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_2522])).
% 4.63/1.91  tff(c_2554, plain, (~l1_pre_topc('#skF_10')), inference(resolution, [status(thm)], [c_66, c_2531])).
% 4.63/1.91  tff(c_2558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2455, c_2554])).
% 4.63/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.91  
% 4.63/1.91  Inference rules
% 4.63/1.91  ----------------------
% 4.63/1.91  #Ref     : 0
% 4.63/1.91  #Sup     : 495
% 4.63/1.91  #Fact    : 6
% 4.63/1.91  #Define  : 0
% 4.63/1.91  #Split   : 22
% 4.63/1.91  #Chain   : 0
% 4.63/1.91  #Close   : 0
% 4.63/1.91  
% 4.63/1.91  Ordering : KBO
% 4.63/1.91  
% 4.63/1.91  Simplification rules
% 4.63/1.91  ----------------------
% 4.63/1.91  #Subsume      : 86
% 4.63/1.91  #Demod        : 231
% 4.63/1.91  #Tautology    : 105
% 4.63/1.91  #SimpNegUnit  : 41
% 4.63/1.91  #BackRed      : 0
% 4.63/1.91  
% 4.63/1.91  #Partial instantiations: 0
% 4.63/1.91  #Strategies tried      : 1
% 4.63/1.91  
% 4.63/1.91  Timing (in seconds)
% 4.63/1.91  ----------------------
% 4.63/1.91  Preprocessing        : 0.33
% 4.63/1.91  Parsing              : 0.16
% 4.63/1.91  CNF conversion       : 0.03
% 4.63/1.91  Main loop            : 0.73
% 4.63/1.91  Inferencing          : 0.22
% 4.63/1.91  Reduction            : 0.23
% 4.63/1.91  Demodulation         : 0.16
% 4.63/1.91  BG Simplification    : 0.03
% 4.63/1.91  Subsumption          : 0.18
% 4.63/1.91  Abstraction          : 0.03
% 4.63/1.91  MUC search           : 0.00
% 4.63/1.91  Cooper               : 0.00
% 4.63/1.91  Total                : 1.11
% 4.63/1.91  Index Insertion      : 0.00
% 4.63/1.91  Index Deletion       : 0.00
% 4.63/1.91  Index Matching       : 0.00
% 4.63/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------

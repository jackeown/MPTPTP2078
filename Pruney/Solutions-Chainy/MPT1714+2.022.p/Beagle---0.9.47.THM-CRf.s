%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:35 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 367 expanded)
%              Number of leaves         :   35 ( 130 expanded)
%              Depth                    :   13
%              Number of atoms          :  201 (1290 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_58,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_958,plain,(
    ! [B_143,A_144] :
      ( l1_pre_topc(B_143)
      | ~ m1_pre_topc(B_143,A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_961,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_958])).

tff(c_973,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_961])).

tff(c_38,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_58,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_970,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_958])).

tff(c_980,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_970])).

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_977,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_958])).

tff(c_981,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_977])).

tff(c_995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_981])).

tff(c_996,plain,(
    l1_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_977])).

tff(c_835,plain,(
    ! [B_127,A_128] :
      ( l1_pre_topc(B_127)
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_847,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_835])).

tff(c_857,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_847])).

tff(c_838,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_835])).

tff(c_850,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_838])).

tff(c_88,plain,(
    ! [B_70,A_71] :
      ( l1_pre_topc(B_70)
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_88])).

tff(c_110,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_100])).

tff(c_107,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_88])).

tff(c_111,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_111])).

tff(c_126,plain,(
    l1_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_28,plain,(
    ! [B_29,A_7] :
      ( r1_tarski(k2_struct_0(B_29),k2_struct_0(A_7))
      | ~ m1_pre_topc(B_29,A_7)
      | ~ l1_pre_topc(B_29)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_103,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_91])).

tff(c_48,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_73,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_165,plain,(
    ! [B_79,A_80] :
      ( r1_tsep_1(B_79,A_80)
      | ~ r1_tsep_1(A_80,B_79)
      | ~ l1_struct_0(B_79)
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_168,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_73,c_165])).

tff(c_169,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_172,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_169])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_172])).

tff(c_177,plain,
    ( ~ l1_struct_0('#skF_7')
    | r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_184,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_187,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_184])).

tff(c_191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_187])).

tff(c_193,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_192,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_74,plain,(
    ! [A_68] :
      ( u1_struct_0(A_68) = k2_struct_0(A_68)
      | ~ l1_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_38,c_74])).

tff(c_131,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_103,c_78])).

tff(c_178,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_136,plain,(
    u1_struct_0('#skF_6') = k2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_110,c_78])).

tff(c_226,plain,(
    ! [A_90,B_91] :
      ( r1_xboole_0(u1_struct_0(A_90),u1_struct_0(B_91))
      | ~ r1_tsep_1(A_90,B_91)
      | ~ l1_struct_0(B_91)
      | ~ l1_struct_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_235,plain,(
    ! [A_90] :
      ( r1_xboole_0(u1_struct_0(A_90),k2_struct_0('#skF_6'))
      | ~ r1_tsep_1(A_90,'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | ~ l1_struct_0(A_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_226])).

tff(c_423,plain,(
    ! [A_100] :
      ( r1_xboole_0(u1_struct_0(A_100),k2_struct_0('#skF_6'))
      | ~ r1_tsep_1(A_100,'#skF_6')
      | ~ l1_struct_0(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_235])).

tff(c_432,plain,
    ( r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6'))
    | ~ r1_tsep_1('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_423])).

tff(c_443,plain,(
    r1_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_192,c_432])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = A_1
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_449,plain,(
    k4_xboole_0(k2_struct_0('#skF_7'),k2_struct_0('#skF_6')) = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_443,c_2])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,k4_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_483,plain,(
    ! [A_3] :
      ( r1_xboole_0(A_3,k2_struct_0('#skF_7'))
      | ~ r1_tarski(A_3,k2_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_449,c_6])).

tff(c_50,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_141,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_78])).

tff(c_316,plain,(
    ! [A_93,B_94] :
      ( r1_tsep_1(A_93,B_94)
      | ~ r1_xboole_0(u1_struct_0(A_93),u1_struct_0(B_94))
      | ~ l1_struct_0(B_94)
      | ~ l1_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_334,plain,(
    ! [A_93] :
      ( r1_tsep_1(A_93,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_93),k2_struct_0('#skF_7'))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_316])).

tff(c_715,plain,(
    ! [A_119] :
      ( r1_tsep_1(A_119,'#skF_7')
      | ~ r1_xboole_0(u1_struct_0(A_119),k2_struct_0('#skF_7'))
      | ~ l1_struct_0(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_334])).

tff(c_730,plain,
    ( r1_tsep_1('#skF_5','#skF_7')
    | ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_715])).

tff(c_741,plain,
    ( ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7'))
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_730])).

tff(c_745,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_748,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_745])).

tff(c_752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_748])).

tff(c_753,plain,(
    ~ r1_xboole_0(k2_struct_0('#skF_5'),k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_774,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_483,c_753])).

tff(c_813,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_774])).

tff(c_817,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_126,c_52,c_813])).

tff(c_819,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_818,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_912,plain,(
    ! [B_137,A_138] :
      ( r1_tsep_1(B_137,A_138)
      | ~ r1_tsep_1(A_138,B_137)
      | ~ l1_struct_0(B_137)
      | ~ l1_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_914,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_818,c_912])).

tff(c_917,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_914])).

tff(c_918,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_917])).

tff(c_921,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_918])).

tff(c_925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_921])).

tff(c_926,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_917])).

tff(c_935,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_926])).

tff(c_939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_935])).

tff(c_940,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_941,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1052,plain,(
    ! [B_153,A_154] :
      ( r1_tsep_1(B_153,A_154)
      | ~ r1_tsep_1(A_154,B_153)
      | ~ l1_struct_0(B_153)
      | ~ l1_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1056,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_941,c_1052])).

tff(c_1060,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_940,c_1056])).

tff(c_1061,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_1064,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1061])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_1064])).

tff(c_1069,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_1073,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_1069])).

tff(c_1077,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_973,c_1073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.53  
% 3.34/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/1.53  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.34/1.53  
% 3.34/1.53  %Foreground sorts:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Background operators:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Foreground operators:
% 3.34/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.34/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.34/1.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.34/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.34/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.34/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.53  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.34/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.34/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.34/1.53  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.34/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.34/1.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.34/1.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.34/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.53  
% 3.61/1.56  tff(f_124, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.61/1.56  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.61/1.56  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.61/1.56  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.61/1.56  tff(f_86, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.61/1.56  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.61/1.56  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.61/1.56  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.61/1.56  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.61/1.56  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.56  tff(c_54, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.56  tff(c_958, plain, (![B_143, A_144]: (l1_pre_topc(B_143) | ~m1_pre_topc(B_143, A_144) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.61/1.56  tff(c_961, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_958])).
% 3.61/1.56  tff(c_973, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_961])).
% 3.61/1.56  tff(c_38, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.61/1.56  tff(c_58, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.56  tff(c_970, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_958])).
% 3.61/1.56  tff(c_980, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_970])).
% 3.61/1.56  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.56  tff(c_977, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_52, c_958])).
% 3.61/1.56  tff(c_981, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_977])).
% 3.61/1.56  tff(c_995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_980, c_981])).
% 3.61/1.56  tff(c_996, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_977])).
% 3.61/1.56  tff(c_835, plain, (![B_127, A_128]: (l1_pre_topc(B_127) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.61/1.56  tff(c_847, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_835])).
% 3.61/1.56  tff(c_857, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_847])).
% 3.61/1.56  tff(c_838, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_835])).
% 3.61/1.56  tff(c_850, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_838])).
% 3.61/1.56  tff(c_88, plain, (![B_70, A_71]: (l1_pre_topc(B_70) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.61/1.56  tff(c_100, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_88])).
% 3.61/1.56  tff(c_110, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_100])).
% 3.61/1.56  tff(c_107, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_52, c_88])).
% 3.61/1.56  tff(c_111, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_107])).
% 3.61/1.56  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_111])).
% 3.61/1.56  tff(c_126, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_107])).
% 3.61/1.56  tff(c_28, plain, (![B_29, A_7]: (r1_tarski(k2_struct_0(B_29), k2_struct_0(A_7)) | ~m1_pre_topc(B_29, A_7) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.61/1.56  tff(c_91, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_88])).
% 3.61/1.56  tff(c_103, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_91])).
% 3.61/1.56  tff(c_48, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.56  tff(c_73, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_48])).
% 3.61/1.56  tff(c_165, plain, (![B_79, A_80]: (r1_tsep_1(B_79, A_80) | ~r1_tsep_1(A_80, B_79) | ~l1_struct_0(B_79) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.56  tff(c_168, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_73, c_165])).
% 3.61/1.56  tff(c_169, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_168])).
% 3.61/1.56  tff(c_172, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_38, c_169])).
% 3.61/1.56  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_172])).
% 3.61/1.56  tff(c_177, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_168])).
% 3.61/1.56  tff(c_184, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_177])).
% 3.61/1.56  tff(c_187, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_184])).
% 3.61/1.56  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_187])).
% 3.61/1.56  tff(c_193, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_177])).
% 3.61/1.56  tff(c_192, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_177])).
% 3.61/1.56  tff(c_74, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.61/1.56  tff(c_78, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_38, c_74])).
% 3.61/1.56  tff(c_131, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_103, c_78])).
% 3.61/1.56  tff(c_178, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_168])).
% 3.61/1.56  tff(c_136, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_110, c_78])).
% 3.61/1.56  tff(c_226, plain, (![A_90, B_91]: (r1_xboole_0(u1_struct_0(A_90), u1_struct_0(B_91)) | ~r1_tsep_1(A_90, B_91) | ~l1_struct_0(B_91) | ~l1_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.56  tff(c_235, plain, (![A_90]: (r1_xboole_0(u1_struct_0(A_90), k2_struct_0('#skF_6')) | ~r1_tsep_1(A_90, '#skF_6') | ~l1_struct_0('#skF_6') | ~l1_struct_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_136, c_226])).
% 3.61/1.56  tff(c_423, plain, (![A_100]: (r1_xboole_0(u1_struct_0(A_100), k2_struct_0('#skF_6')) | ~r1_tsep_1(A_100, '#skF_6') | ~l1_struct_0(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_235])).
% 3.61/1.56  tff(c_432, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_131, c_423])).
% 3.61/1.56  tff(c_443, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_192, c_432])).
% 3.61/1.56  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.61/1.56  tff(c_449, plain, (k4_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_443, c_2])).
% 3.61/1.56  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.61/1.56  tff(c_483, plain, (![A_3]: (r1_xboole_0(A_3, k2_struct_0('#skF_7')) | ~r1_tarski(A_3, k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_449, c_6])).
% 3.61/1.56  tff(c_50, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.61/1.56  tff(c_72, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 3.61/1.56  tff(c_141, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_126, c_78])).
% 3.61/1.56  tff(c_316, plain, (![A_93, B_94]: (r1_tsep_1(A_93, B_94) | ~r1_xboole_0(u1_struct_0(A_93), u1_struct_0(B_94)) | ~l1_struct_0(B_94) | ~l1_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.61/1.56  tff(c_334, plain, (![A_93]: (r1_tsep_1(A_93, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_93), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_93))), inference(superposition, [status(thm), theory('equality')], [c_131, c_316])).
% 3.61/1.56  tff(c_715, plain, (![A_119]: (r1_tsep_1(A_119, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_119), k2_struct_0('#skF_7')) | ~l1_struct_0(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_334])).
% 3.61/1.56  tff(c_730, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_141, c_715])).
% 3.61/1.56  tff(c_741, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_730])).
% 3.61/1.56  tff(c_745, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_741])).
% 3.61/1.56  tff(c_748, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_745])).
% 3.61/1.56  tff(c_752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_748])).
% 3.61/1.56  tff(c_753, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_741])).
% 3.61/1.56  tff(c_774, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_483, c_753])).
% 3.61/1.56  tff(c_813, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_28, c_774])).
% 3.61/1.56  tff(c_817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_126, c_52, c_813])).
% 3.61/1.56  tff(c_819, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 3.61/1.56  tff(c_818, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_48])).
% 3.61/1.56  tff(c_912, plain, (![B_137, A_138]: (r1_tsep_1(B_137, A_138) | ~r1_tsep_1(A_138, B_137) | ~l1_struct_0(B_137) | ~l1_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.56  tff(c_914, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_818, c_912])).
% 3.61/1.56  tff(c_917, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_819, c_914])).
% 3.61/1.56  tff(c_918, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_917])).
% 3.61/1.56  tff(c_921, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_918])).
% 3.61/1.56  tff(c_925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_921])).
% 3.61/1.56  tff(c_926, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_917])).
% 3.61/1.56  tff(c_935, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_38, c_926])).
% 3.61/1.56  tff(c_939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_857, c_935])).
% 3.61/1.56  tff(c_940, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_50])).
% 3.61/1.56  tff(c_941, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 3.61/1.56  tff(c_1052, plain, (![B_153, A_154]: (r1_tsep_1(B_153, A_154) | ~r1_tsep_1(A_154, B_153) | ~l1_struct_0(B_153) | ~l1_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.61/1.56  tff(c_1056, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_941, c_1052])).
% 3.61/1.56  tff(c_1060, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_940, c_1056])).
% 3.61/1.56  tff(c_1061, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_1060])).
% 3.61/1.56  tff(c_1064, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1061])).
% 3.61/1.56  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_996, c_1064])).
% 3.61/1.56  tff(c_1069, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_1060])).
% 3.61/1.56  tff(c_1073, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_1069])).
% 3.61/1.56  tff(c_1077, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_973, c_1073])).
% 3.61/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.56  
% 3.61/1.56  Inference rules
% 3.61/1.56  ----------------------
% 3.61/1.56  #Ref     : 0
% 3.61/1.56  #Sup     : 217
% 3.61/1.56  #Fact    : 0
% 3.61/1.56  #Define  : 0
% 3.61/1.56  #Split   : 18
% 3.61/1.56  #Chain   : 0
% 3.61/1.56  #Close   : 0
% 3.61/1.56  
% 3.61/1.56  Ordering : KBO
% 3.61/1.56  
% 3.61/1.56  Simplification rules
% 3.61/1.56  ----------------------
% 3.61/1.56  #Subsume      : 10
% 3.61/1.56  #Demod        : 112
% 3.61/1.56  #Tautology    : 58
% 3.61/1.56  #SimpNegUnit  : 14
% 3.61/1.56  #BackRed      : 0
% 3.61/1.56  
% 3.61/1.56  #Partial instantiations: 0
% 3.61/1.56  #Strategies tried      : 1
% 3.61/1.56  
% 3.61/1.56  Timing (in seconds)
% 3.61/1.56  ----------------------
% 3.61/1.56  Preprocessing        : 0.35
% 3.61/1.56  Parsing              : 0.18
% 3.61/1.56  CNF conversion       : 0.03
% 3.61/1.56  Main loop            : 0.41
% 3.61/1.56  Inferencing          : 0.14
% 3.61/1.56  Reduction            : 0.13
% 3.61/1.56  Demodulation         : 0.08
% 3.61/1.56  BG Simplification    : 0.03
% 3.61/1.56  Subsumption          : 0.08
% 3.61/1.56  Abstraction          : 0.02
% 3.61/1.56  MUC search           : 0.00
% 3.61/1.56  Cooper               : 0.00
% 3.61/1.56  Total                : 0.81
% 3.61/1.56  Index Insertion      : 0.00
% 3.61/1.56  Index Deletion       : 0.00
% 3.61/1.56  Index Matching       : 0.00
% 3.61/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------

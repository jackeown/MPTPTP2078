%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:39 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 354 expanded)
%              Number of leaves         :   35 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 (1241 expanded)
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
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_66,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_961,plain,(
    ! [B_141,A_142] :
      ( l1_pre_topc(B_141)
      | ~ m1_pre_topc(B_141,A_142)
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_973,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_961])).

tff(c_983,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_973])).

tff(c_38,plain,(
    ! [A_47] :
      ( l1_struct_0(A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    m1_pre_topc('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_964,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_961])).

tff(c_976,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_964])).

tff(c_835,plain,(
    ! [B_127,A_128] :
      ( l1_pre_topc(B_127)
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_838,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_835])).

tff(c_850,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_838])).

tff(c_62,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_841,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_835])).

tff(c_853,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_841])).

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

tff(c_52,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

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

tff(c_50,plain,
    ( r1_tsep_1('#skF_7','#skF_6')
    | r1_tsep_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_72,plain,(
    r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_50])).

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
    inference(resolution,[status(thm)],[c_72,c_165])).

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

tff(c_48,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_5')
    | ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_73,plain,(
    ~ r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_48])).

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
    inference(negUnitSimplification,[status(thm)],[c_73,c_730])).

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

tff(c_818,plain,(
    ~ r1_tsep_1('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_819,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_912,plain,(
    ! [B_137,A_138] :
      ( r1_tsep_1(B_137,A_138)
      | ~ r1_tsep_1(A_138,B_137)
      | ~ l1_struct_0(B_137)
      | ~ l1_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_914,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_819,c_912])).

tff(c_919,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_818,c_914])).

tff(c_921,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_919])).

tff(c_924,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_921])).

tff(c_928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_924])).

tff(c_929,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_919])).

tff(c_939,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_929])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_939])).

tff(c_945,plain,(
    ~ r1_tsep_1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_944,plain,(
    r1_tsep_1('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1038,plain,(
    ! [B_150,A_151] :
      ( r1_tsep_1(B_150,A_151)
      | ~ r1_tsep_1(A_151,B_150)
      | ~ l1_struct_0(B_150)
      | ~ l1_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1040,plain,
    ( r1_tsep_1('#skF_6','#skF_7')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_944,c_1038])).

tff(c_1043,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_945,c_1040])).

tff(c_1044,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1043])).

tff(c_1047,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_1044])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_1047])).

tff(c_1052,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1043])).

tff(c_1056,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_1052])).

tff(c_1060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_983,c_1056])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.49  
% 3.33/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.50  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 3.33/1.50  
% 3.33/1.50  %Foreground sorts:
% 3.33/1.50  
% 3.33/1.50  
% 3.33/1.50  %Background operators:
% 3.33/1.50  
% 3.33/1.50  
% 3.33/1.50  %Foreground operators:
% 3.33/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.33/1.50  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.33/1.50  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.33/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.33/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.33/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.33/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.33/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.33/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.33/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.33/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.33/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.33/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.33/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.33/1.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.33/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.33/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.33/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.33/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.33/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.33/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.33/1.50  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.33/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.33/1.50  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.33/1.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.33/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.33/1.50  
% 3.33/1.51  tff(f_124, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tmap_1)).
% 3.33/1.51  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.33/1.51  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.33/1.51  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(B, A) <=> (r1_tarski(k2_struct_0(B), k2_struct_0(A)) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (r2_hidden(C, u1_pre_topc(B)) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & r2_hidden(D, u1_pre_topc(A))) & (C = k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 3.33/1.51  tff(f_86, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.33/1.51  tff(f_37, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 3.33/1.51  tff(f_78, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 3.33/1.51  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.33/1.51  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.33/1.51  tff(c_66, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.33/1.51  tff(c_58, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.33/1.51  tff(c_961, plain, (![B_141, A_142]: (l1_pre_topc(B_141) | ~m1_pre_topc(B_141, A_142) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.51  tff(c_973, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_961])).
% 3.33/1.51  tff(c_983, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_973])).
% 3.33/1.51  tff(c_38, plain, (![A_47]: (l1_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.33/1.51  tff(c_54, plain, (m1_pre_topc('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.33/1.51  tff(c_964, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_961])).
% 3.33/1.51  tff(c_976, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_964])).
% 3.33/1.51  tff(c_835, plain, (![B_127, A_128]: (l1_pre_topc(B_127) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.51  tff(c_838, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_835])).
% 3.33/1.51  tff(c_850, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_838])).
% 3.33/1.51  tff(c_62, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.33/1.51  tff(c_841, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_62, c_835])).
% 3.33/1.51  tff(c_853, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_841])).
% 3.33/1.51  tff(c_88, plain, (![B_70, A_71]: (l1_pre_topc(B_70) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.33/1.51  tff(c_100, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_58, c_88])).
% 3.33/1.51  tff(c_110, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_100])).
% 3.33/1.51  tff(c_52, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.33/1.51  tff(c_107, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_52, c_88])).
% 3.33/1.51  tff(c_111, plain, (~l1_pre_topc('#skF_6')), inference(splitLeft, [status(thm)], [c_107])).
% 3.33/1.51  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_111])).
% 3.33/1.51  tff(c_126, plain, (l1_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_107])).
% 3.33/1.51  tff(c_28, plain, (![B_29, A_7]: (r1_tarski(k2_struct_0(B_29), k2_struct_0(A_7)) | ~m1_pre_topc(B_29, A_7) | ~l1_pre_topc(B_29) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.33/1.51  tff(c_91, plain, (l1_pre_topc('#skF_7') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_88])).
% 3.33/1.51  tff(c_103, plain, (l1_pre_topc('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_91])).
% 3.33/1.51  tff(c_50, plain, (r1_tsep_1('#skF_7', '#skF_6') | r1_tsep_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.33/1.51  tff(c_72, plain, (r1_tsep_1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_50])).
% 3.33/1.51  tff(c_165, plain, (![B_79, A_80]: (r1_tsep_1(B_79, A_80) | ~r1_tsep_1(A_80, B_79) | ~l1_struct_0(B_79) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.51  tff(c_168, plain, (r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_72, c_165])).
% 3.33/1.51  tff(c_169, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_168])).
% 3.33/1.51  tff(c_172, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_38, c_169])).
% 3.33/1.51  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_172])).
% 3.33/1.51  tff(c_177, plain, (~l1_struct_0('#skF_7') | r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_168])).
% 3.33/1.51  tff(c_184, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_177])).
% 3.33/1.51  tff(c_187, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_184])).
% 3.33/1.51  tff(c_191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_187])).
% 3.33/1.51  tff(c_193, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_177])).
% 3.33/1.51  tff(c_192, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_177])).
% 3.33/1.51  tff(c_74, plain, (![A_68]: (u1_struct_0(A_68)=k2_struct_0(A_68) | ~l1_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.51  tff(c_78, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_38, c_74])).
% 3.33/1.51  tff(c_131, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_103, c_78])).
% 3.33/1.51  tff(c_178, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_168])).
% 3.33/1.51  tff(c_136, plain, (u1_struct_0('#skF_6')=k2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_110, c_78])).
% 3.33/1.51  tff(c_226, plain, (![A_90, B_91]: (r1_xboole_0(u1_struct_0(A_90), u1_struct_0(B_91)) | ~r1_tsep_1(A_90, B_91) | ~l1_struct_0(B_91) | ~l1_struct_0(A_90))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.33/1.51  tff(c_235, plain, (![A_90]: (r1_xboole_0(u1_struct_0(A_90), k2_struct_0('#skF_6')) | ~r1_tsep_1(A_90, '#skF_6') | ~l1_struct_0('#skF_6') | ~l1_struct_0(A_90))), inference(superposition, [status(thm), theory('equality')], [c_136, c_226])).
% 3.33/1.51  tff(c_423, plain, (![A_100]: (r1_xboole_0(u1_struct_0(A_100), k2_struct_0('#skF_6')) | ~r1_tsep_1(A_100, '#skF_6') | ~l1_struct_0(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_178, c_235])).
% 3.33/1.51  tff(c_432, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6')) | ~r1_tsep_1('#skF_7', '#skF_6') | ~l1_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_131, c_423])).
% 3.33/1.51  tff(c_443, plain, (r1_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_192, c_432])).
% 3.33/1.51  tff(c_2, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=A_1 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.51  tff(c_449, plain, (k4_xboole_0(k2_struct_0('#skF_7'), k2_struct_0('#skF_6'))=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_443, c_2])).
% 3.33/1.51  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, k4_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.51  tff(c_483, plain, (![A_3]: (r1_xboole_0(A_3, k2_struct_0('#skF_7')) | ~r1_tarski(A_3, k2_struct_0('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_449, c_6])).
% 3.33/1.51  tff(c_48, plain, (~r1_tsep_1('#skF_7', '#skF_5') | ~r1_tsep_1('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.33/1.51  tff(c_73, plain, (~r1_tsep_1('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_48])).
% 3.33/1.51  tff(c_141, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_126, c_78])).
% 3.33/1.51  tff(c_316, plain, (![A_93, B_94]: (r1_tsep_1(A_93, B_94) | ~r1_xboole_0(u1_struct_0(A_93), u1_struct_0(B_94)) | ~l1_struct_0(B_94) | ~l1_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.33/1.51  tff(c_334, plain, (![A_93]: (r1_tsep_1(A_93, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_93), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_7') | ~l1_struct_0(A_93))), inference(superposition, [status(thm), theory('equality')], [c_131, c_316])).
% 3.33/1.51  tff(c_715, plain, (![A_119]: (r1_tsep_1(A_119, '#skF_7') | ~r1_xboole_0(u1_struct_0(A_119), k2_struct_0('#skF_7')) | ~l1_struct_0(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_334])).
% 3.33/1.51  tff(c_730, plain, (r1_tsep_1('#skF_5', '#skF_7') | ~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_141, c_715])).
% 3.33/1.51  tff(c_741, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7')) | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_73, c_730])).
% 3.33/1.51  tff(c_745, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_741])).
% 3.33/1.51  tff(c_748, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_745])).
% 3.33/1.51  tff(c_752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_748])).
% 3.33/1.51  tff(c_753, plain, (~r1_xboole_0(k2_struct_0('#skF_5'), k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_741])).
% 3.33/1.51  tff(c_774, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_483, c_753])).
% 3.33/1.51  tff(c_813, plain, (~m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_28, c_774])).
% 3.33/1.51  tff(c_817, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_126, c_52, c_813])).
% 3.33/1.51  tff(c_818, plain, (~r1_tsep_1('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_48])).
% 3.33/1.51  tff(c_819, plain, (r1_tsep_1('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_48])).
% 3.33/1.51  tff(c_912, plain, (![B_137, A_138]: (r1_tsep_1(B_137, A_138) | ~r1_tsep_1(A_138, B_137) | ~l1_struct_0(B_137) | ~l1_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.51  tff(c_914, plain, (r1_tsep_1('#skF_7', '#skF_5') | ~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_819, c_912])).
% 3.33/1.51  tff(c_919, plain, (~l1_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_818, c_914])).
% 3.33/1.51  tff(c_921, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_919])).
% 3.33/1.51  tff(c_924, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_921])).
% 3.33/1.51  tff(c_928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_853, c_924])).
% 3.33/1.51  tff(c_929, plain, (~l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_919])).
% 3.33/1.51  tff(c_939, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_929])).
% 3.33/1.51  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_850, c_939])).
% 3.33/1.51  tff(c_945, plain, (~r1_tsep_1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 3.33/1.51  tff(c_944, plain, (r1_tsep_1('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_50])).
% 3.33/1.51  tff(c_1038, plain, (![B_150, A_151]: (r1_tsep_1(B_150, A_151) | ~r1_tsep_1(A_151, B_150) | ~l1_struct_0(B_150) | ~l1_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.33/1.51  tff(c_1040, plain, (r1_tsep_1('#skF_6', '#skF_7') | ~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_944, c_1038])).
% 3.33/1.51  tff(c_1043, plain, (~l1_struct_0('#skF_6') | ~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_945, c_1040])).
% 3.33/1.51  tff(c_1044, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1043])).
% 3.33/1.51  tff(c_1047, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_38, c_1044])).
% 3.33/1.52  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_976, c_1047])).
% 3.33/1.52  tff(c_1052, plain, (~l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1043])).
% 3.33/1.52  tff(c_1056, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_38, c_1052])).
% 3.33/1.52  tff(c_1060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_983, c_1056])).
% 3.33/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.33/1.52  
% 3.33/1.52  Inference rules
% 3.33/1.52  ----------------------
% 3.33/1.52  #Ref     : 0
% 3.33/1.52  #Sup     : 212
% 3.33/1.52  #Fact    : 0
% 3.33/1.52  #Define  : 0
% 3.33/1.52  #Split   : 19
% 3.33/1.52  #Chain   : 0
% 3.33/1.52  #Close   : 0
% 3.33/1.52  
% 3.33/1.52  Ordering : KBO
% 3.33/1.52  
% 3.33/1.52  Simplification rules
% 3.33/1.52  ----------------------
% 3.33/1.52  #Subsume      : 10
% 3.33/1.52  #Demod        : 112
% 3.33/1.52  #Tautology    : 56
% 3.33/1.52  #SimpNegUnit  : 14
% 3.33/1.52  #BackRed      : 0
% 3.33/1.52  
% 3.33/1.52  #Partial instantiations: 0
% 3.33/1.52  #Strategies tried      : 1
% 3.33/1.52  
% 3.33/1.52  Timing (in seconds)
% 3.33/1.52  ----------------------
% 3.33/1.52  Preprocessing        : 0.34
% 3.33/1.52  Parsing              : 0.17
% 3.33/1.52  CNF conversion       : 0.03
% 3.33/1.52  Main loop            : 0.41
% 3.33/1.52  Inferencing          : 0.14
% 3.33/1.52  Reduction            : 0.13
% 3.33/1.52  Demodulation         : 0.08
% 3.33/1.52  BG Simplification    : 0.03
% 3.33/1.52  Subsumption          : 0.08
% 3.33/1.52  Abstraction          : 0.02
% 3.33/1.52  MUC search           : 0.00
% 3.33/1.52  Cooper               : 0.00
% 3.33/1.52  Total                : 0.80
% 3.33/1.52  Index Insertion      : 0.00
% 3.33/1.52  Index Deletion       : 0.00
% 3.33/1.52  Index Matching       : 0.00
% 3.33/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:26:30 EST 2020

% Result     : Theorem 57.05s
% Output     : CNFRefutation 57.25s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 368 expanded)
%              Number of leaves         :   46 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  279 ( 967 expanded)
%              Number of equality atoms :   19 (  59 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_176,negated_conjecture,(
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
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_141,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_88,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_86,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_148,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_105,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_60,axiom,(
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

tff(f_133,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_80,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_76,plain,(
    m1_pre_topc('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_256774,plain,(
    ! [B_2396,A_2397] :
      ( l1_pre_topc(B_2396)
      | ~ m1_pre_topc(B_2396,A_2397)
      | ~ l1_pre_topc(A_2397) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_256777,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_256774])).

tff(c_256786,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_256777])).

tff(c_54,plain,(
    ! [A_37] :
      ( l1_struct_0(A_37)
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_72,plain,(
    m1_pre_topc('#skF_9','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_256780,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_256774])).

tff(c_256789,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_256780])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_124,plain,(
    ! [B_70,A_71] :
      ( l1_pre_topc(B_70)
      | ~ m1_pre_topc(B_70,A_71)
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_127,plain,
    ( l1_pre_topc('#skF_8')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_76,c_124])).

tff(c_136,plain,(
    l1_pre_topc('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_127])).

tff(c_68,plain,
    ( r1_tsep_1('#skF_9','#skF_8')
    | r1_tsep_1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_91,plain,(
    r1_tsep_1('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_701,plain,(
    ! [B_143,A_144] :
      ( r1_tsep_1(B_143,A_144)
      | ~ r1_tsep_1(A_144,B_143)
      | ~ l1_struct_0(B_143)
      | ~ l1_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_704,plain,
    ( r1_tsep_1('#skF_9','#skF_8')
    | ~ l1_struct_0('#skF_9')
    | ~ l1_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_91,c_701])).

tff(c_728,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_704])).

tff(c_731,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_728])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_731])).

tff(c_737,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_27] : r1_xboole_0(A_27,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_92,plain,(
    ! [B_60,A_61] :
      ( r1_xboole_0(B_60,A_61)
      | ~ r1_xboole_0(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_95,plain,(
    ! [A_27] : r1_xboole_0(k1_xboole_0,A_27) ),
    inference(resolution,[status(thm)],[c_34,c_92])).

tff(c_32,plain,(
    ! [A_26] : r1_tarski(k1_xboole_0,A_26) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_159,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_170,plain,(
    ! [A_26] : k3_xboole_0(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_159])).

tff(c_221,plain,(
    ! [A_87,B_88,C_89] :
      ( ~ r1_xboole_0(A_87,B_88)
      | ~ r2_hidden(C_89,k3_xboole_0(A_87,B_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_231,plain,(
    ! [A_26,C_89] :
      ( ~ r1_xboole_0(k1_xboole_0,A_26)
      | ~ r2_hidden(C_89,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_221])).

tff(c_240,plain,(
    ! [C_90] : ~ r2_hidden(C_90,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_231])).

tff(c_250,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_240])).

tff(c_130,plain,
    ( l1_pre_topc('#skF_9')
    | ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_124])).

tff(c_139,plain,(
    l1_pre_topc('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_130])).

tff(c_70,plain,(
    m1_pre_topc('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_66,plain,(
    ! [B_49,A_47] :
      ( m1_subset_1(u1_struct_0(B_49),k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_112,plain,(
    ! [C_66,A_67] :
      ( r1_tarski(C_66,A_67)
      | ~ r2_hidden(C_66,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_753,plain,(
    ! [A_147] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_147)),A_147)
      | v1_xboole_0(k1_zfmisc_1(A_147)) ) ),
    inference(resolution,[status(thm)],[c_4,c_112])).

tff(c_208,plain,(
    ! [B_85,A_86] :
      ( B_85 = A_86
      | ~ r1_tarski(B_85,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_216,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_208])).

tff(c_767,plain,
    ( '#skF_1'(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_753,c_216])).

tff(c_771,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_141,plain,(
    ! [C_72,A_73] :
      ( r2_hidden(C_72,k1_zfmisc_1(A_73))
      | ~ r1_tarski(C_72,A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [A_73,C_72] :
      ( ~ v1_xboole_0(k1_zfmisc_1(A_73))
      | ~ r1_tarski(C_72,A_73) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_840,plain,(
    ! [C_152] : ~ r1_tarski(C_152,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_771,c_149])).

tff(c_867,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_32,c_840])).

tff(c_869,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_380,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_2'(A_107,B_108),A_107)
      | r1_tarski(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_36,plain,(
    ! [C_32,A_28] :
      ( r1_tarski(C_32,A_28)
      | ~ r2_hidden(C_32,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1638,plain,(
    ! [A_205,B_206] :
      ( r1_tarski('#skF_2'(k1_zfmisc_1(A_205),B_206),A_205)
      | r1_tarski(k1_zfmisc_1(A_205),B_206) ) ),
    inference(resolution,[status(thm)],[c_380,c_36])).

tff(c_1695,plain,(
    ! [B_209] :
      ( '#skF_2'(k1_zfmisc_1(k1_xboole_0),B_209) = k1_xboole_0
      | r1_tarski(k1_zfmisc_1(k1_xboole_0),B_209) ) ),
    inference(resolution,[status(thm)],[c_1638,c_216])).

tff(c_481,plain,(
    ! [C_121,B_122,A_123] :
      ( r2_hidden(C_121,B_122)
      | ~ r2_hidden(C_121,A_123)
      | ~ r1_tarski(A_123,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1045,plain,(
    ! [A_165,B_166] :
      ( r2_hidden('#skF_1'(A_165),B_166)
      | ~ r1_tarski(A_165,B_166)
      | v1_xboole_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_4,c_481])).

tff(c_1070,plain,(
    ! [B_166,A_165] :
      ( ~ v1_xboole_0(B_166)
      | ~ r1_tarski(A_165,B_166)
      | v1_xboole_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_1045,c_2])).

tff(c_1698,plain,(
    ! [B_209] :
      ( ~ v1_xboole_0(B_209)
      | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
      | '#skF_2'(k1_zfmisc_1(k1_xboole_0),B_209) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1695,c_1070])).

tff(c_1763,plain,(
    ! [B_212] :
      ( ~ v1_xboole_0(B_212)
      | '#skF_2'(k1_zfmisc_1(k1_xboole_0),B_212) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_1698])).

tff(c_38,plain,(
    ! [C_32,A_28] :
      ( r2_hidden(C_32,k1_zfmisc_1(A_28))
      | ~ r1_tarski(C_32,A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_369,plain,(
    ! [A_105,B_106] :
      ( ~ r2_hidden('#skF_2'(A_105,B_106),B_106)
      | r1_tarski(A_105,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_379,plain,(
    ! [A_105,A_28] :
      ( r1_tarski(A_105,k1_zfmisc_1(A_28))
      | ~ r1_tarski('#skF_2'(A_105,k1_zfmisc_1(A_28)),A_28) ) ),
    inference(resolution,[status(thm)],[c_38,c_369])).

tff(c_1770,plain,(
    ! [A_28] :
      ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(A_28))
      | ~ r1_tarski(k1_xboole_0,A_28)
      | ~ v1_xboole_0(k1_zfmisc_1(A_28)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1763,c_379])).

tff(c_1804,plain,(
    ! [A_213] :
      ( r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(A_213))
      | ~ v1_xboole_0(k1_zfmisc_1(A_213)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1770])).

tff(c_1807,plain,(
    ! [A_213] :
      ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_zfmisc_1(A_213)) ) ),
    inference(resolution,[status(thm)],[c_1804,c_1070])).

tff(c_1821,plain,(
    ! [A_213] : ~ v1_xboole_0(k1_zfmisc_1(A_213)) ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_1807])).

tff(c_198,plain,(
    ! [A_83,B_84] :
      ( r2_hidden(A_83,B_84)
      | v1_xboole_0(B_84)
      | ~ m1_subset_1(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_206,plain,(
    ! [A_83,A_28] :
      ( r1_tarski(A_83,A_28)
      | v1_xboole_0(k1_zfmisc_1(A_28))
      | ~ m1_subset_1(A_83,k1_zfmisc_1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_198,c_36])).

tff(c_2759,plain,(
    ! [A_247,A_248] :
      ( r1_tarski(A_247,A_248)
      | ~ m1_subset_1(A_247,k1_zfmisc_1(A_248)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1821,c_206])).

tff(c_2763,plain,(
    ! [B_49,A_47] :
      ( r1_tarski(u1_struct_0(B_49),u1_struct_0(A_47))
      | ~ m1_pre_topc(B_49,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(resolution,[status(thm)],[c_66,c_2759])).

tff(c_736,plain,
    ( ~ l1_struct_0('#skF_9')
    | r1_tsep_1('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_704])).

tff(c_738,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_741,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_738])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_741])).

tff(c_747,plain,(
    l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_498,plain,(
    ! [A_12,B_13,B_122] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_122)
      | ~ r1_tarski(A_12,B_122)
      | r1_xboole_0(A_12,B_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_481])).

tff(c_907,plain,(
    ! [A_154,B_155] :
      ( r1_xboole_0(u1_struct_0(A_154),u1_struct_0(B_155))
      | ~ r1_tsep_1(A_154,B_155)
      | ~ l1_struct_0(B_155)
      | ~ l1_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_14,plain,(
    ! [A_12,B_13,C_16] :
      ( ~ r1_xboole_0(A_12,B_13)
      | ~ r2_hidden(C_16,B_13)
      | ~ r2_hidden(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_5918,plain,(
    ! [C_362,B_363,A_364] :
      ( ~ r2_hidden(C_362,u1_struct_0(B_363))
      | ~ r2_hidden(C_362,u1_struct_0(A_364))
      | ~ r1_tsep_1(A_364,B_363)
      | ~ l1_struct_0(B_363)
      | ~ l1_struct_0(A_364) ) ),
    inference(resolution,[status(thm)],[c_907,c_14])).

tff(c_73434,plain,(
    ! [A_1240,B_1241,A_1242,B_1243] :
      ( ~ r2_hidden('#skF_3'(A_1240,B_1241),u1_struct_0(A_1242))
      | ~ r1_tsep_1(A_1242,B_1243)
      | ~ l1_struct_0(B_1243)
      | ~ l1_struct_0(A_1242)
      | ~ r1_tarski(A_1240,u1_struct_0(B_1243))
      | r1_xboole_0(A_1240,B_1241) ) ),
    inference(resolution,[status(thm)],[c_498,c_5918])).

tff(c_255852,plain,(
    ! [A_2385,B_2386,A_2387] :
      ( ~ r1_tsep_1(A_2385,B_2386)
      | ~ l1_struct_0(B_2386)
      | ~ l1_struct_0(A_2385)
      | ~ r1_tarski(A_2387,u1_struct_0(B_2386))
      | r1_xboole_0(A_2387,u1_struct_0(A_2385)) ) ),
    inference(resolution,[status(thm)],[c_16,c_73434])).

tff(c_255856,plain,(
    ! [A_2387] :
      ( ~ l1_struct_0('#skF_9')
      | ~ l1_struct_0('#skF_8')
      | ~ r1_tarski(A_2387,u1_struct_0('#skF_9'))
      | r1_xboole_0(A_2387,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_91,c_255852])).

tff(c_256185,plain,(
    ! [A_2389] :
      ( ~ r1_tarski(A_2389,u1_struct_0('#skF_9'))
      | r1_xboole_0(A_2389,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_747,c_255856])).

tff(c_28,plain,(
    ! [B_23] : r1_tarski(B_23,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_171,plain,(
    ! [B_23] : k3_xboole_0(B_23,B_23) = B_23 ),
    inference(resolution,[status(thm)],[c_28,c_159])).

tff(c_22,plain,(
    ! [A_17,B_18,C_21] :
      ( ~ r1_xboole_0(A_17,B_18)
      | ~ r2_hidden(C_21,k3_xboole_0(A_17,B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_671,plain,(
    ! [A_140,B_141,B_142] :
      ( ~ r1_xboole_0(A_140,B_141)
      | r1_tarski(k3_xboole_0(A_140,B_141),B_142) ) ),
    inference(resolution,[status(thm)],[c_380,c_22])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( B_23 = A_22
      | ~ r1_tarski(B_23,A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_16833,plain,(
    ! [A_567,B_568,B_569] :
      ( k3_xboole_0(A_567,B_568) = B_569
      | ~ r1_tarski(B_569,k3_xboole_0(A_567,B_568))
      | ~ r1_xboole_0(A_567,B_568) ) ),
    inference(resolution,[status(thm)],[c_671,c_24])).

tff(c_16991,plain,(
    ! [B_23,B_569] :
      ( k3_xboole_0(B_23,B_23) = B_569
      | ~ r1_tarski(B_569,B_23)
      | ~ r1_xboole_0(B_23,B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_16833])).

tff(c_17041,plain,(
    ! [B_571,B_570] :
      ( B_571 = B_570
      | ~ r1_tarski(B_570,B_571)
      | ~ r1_xboole_0(B_571,B_571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_16991])).

tff(c_17124,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ r1_xboole_0(A_26,A_26) ) ),
    inference(resolution,[status(thm)],[c_32,c_17041])).

tff(c_256476,plain,
    ( u1_struct_0('#skF_8') = k1_xboole_0
    | ~ r1_tarski(u1_struct_0('#skF_8'),u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_256185,c_17124])).

tff(c_256508,plain,(
    ~ r1_tarski(u1_struct_0('#skF_8'),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_256476])).

tff(c_256521,plain,
    ( ~ m1_pre_topc('#skF_8','#skF_9')
    | ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_2763,c_256508])).

tff(c_256528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_70,c_256521])).

tff(c_256529,plain,(
    u1_struct_0('#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_256476])).

tff(c_58,plain,(
    ! [A_41] :
      ( ~ v1_xboole_0(u1_struct_0(A_41))
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_256657,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_256529,c_58])).

tff(c_256754,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_250,c_256657])).

tff(c_256756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_256754])).

tff(c_256758,plain,(
    ~ r1_tsep_1('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_256757,plain,(
    r1_tsep_1('#skF_9','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_257385,plain,(
    ! [B_2470,A_2471] :
      ( r1_tsep_1(B_2470,A_2471)
      | ~ r1_tsep_1(A_2471,B_2470)
      | ~ l1_struct_0(B_2470)
      | ~ l1_struct_0(A_2471) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_257387,plain,
    ( r1_tsep_1('#skF_8','#skF_9')
    | ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_256757,c_257385])).

tff(c_257390,plain,
    ( ~ l1_struct_0('#skF_8')
    | ~ l1_struct_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_256758,c_257387])).

tff(c_257391,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_257390])).

tff(c_257394,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_257391])).

tff(c_257398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256789,c_257394])).

tff(c_257399,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_257390])).

tff(c_257403,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_257399])).

tff(c_257407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_256786,c_257403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n012.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:43:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 57.05/46.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.25/46.50  
% 57.25/46.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.25/46.50  %$ r2_hidden > r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_9 > #skF_8 > #skF_2 > #skF_5 > #skF_4
% 57.25/46.50  
% 57.25/46.50  %Foreground sorts:
% 57.25/46.50  
% 57.25/46.50  
% 57.25/46.50  %Background operators:
% 57.25/46.50  
% 57.25/46.50  
% 57.25/46.50  %Foreground operators:
% 57.25/46.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 57.25/46.50  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 57.25/46.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 57.25/46.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 57.25/46.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 57.25/46.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 57.25/46.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 57.25/46.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 57.25/46.50  tff('#skF_7', type, '#skF_7': $i).
% 57.25/46.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 57.25/46.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 57.25/46.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 57.25/46.50  tff('#skF_9', type, '#skF_9': $i).
% 57.25/46.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 57.25/46.50  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 57.25/46.50  tff('#skF_8', type, '#skF_8': $i).
% 57.25/46.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 57.25/46.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 57.25/46.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 57.25/46.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 57.25/46.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 57.25/46.50  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 57.25/46.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 57.25/46.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 57.25/46.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 57.25/46.50  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 57.25/46.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 57.25/46.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 57.25/46.50  
% 57.25/46.54  tff(f_176, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 57.25/46.54  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 57.25/46.54  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 57.25/46.54  tff(f_141, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 57.25/46.54  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 57.25/46.54  tff(f_88, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 57.25/46.54  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 57.25/46.54  tff(f_86, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 57.25/46.54  tff(f_84, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 57.25/46.54  tff(f_74, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 57.25/46.54  tff(f_148, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 57.25/46.54  tff(f_95, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 57.25/46.54  tff(f_80, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 57.25/46.54  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 57.25/46.54  tff(f_105, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 57.25/46.54  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 57.25/46.54  tff(f_133, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 57.25/46.54  tff(f_124, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 57.25/46.54  tff(c_80, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_176])).
% 57.25/46.54  tff(c_76, plain, (m1_pre_topc('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_176])).
% 57.25/46.54  tff(c_256774, plain, (![B_2396, A_2397]: (l1_pre_topc(B_2396) | ~m1_pre_topc(B_2396, A_2397) | ~l1_pre_topc(A_2397))), inference(cnfTransformation, [status(thm)], [f_116])).
% 57.25/46.54  tff(c_256777, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_76, c_256774])).
% 57.25/46.54  tff(c_256786, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_256777])).
% 57.25/46.54  tff(c_54, plain, (![A_37]: (l1_struct_0(A_37) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_109])).
% 57.25/46.54  tff(c_72, plain, (m1_pre_topc('#skF_9', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_176])).
% 57.25/46.54  tff(c_256780, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_72, c_256774])).
% 57.25/46.54  tff(c_256789, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_256780])).
% 57.25/46.54  tff(c_78, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_176])).
% 57.25/46.54  tff(c_124, plain, (![B_70, A_71]: (l1_pre_topc(B_70) | ~m1_pre_topc(B_70, A_71) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_116])).
% 57.25/46.54  tff(c_127, plain, (l1_pre_topc('#skF_8') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_76, c_124])).
% 57.25/46.54  tff(c_136, plain, (l1_pre_topc('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_127])).
% 57.25/46.54  tff(c_68, plain, (r1_tsep_1('#skF_9', '#skF_8') | r1_tsep_1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_176])).
% 57.25/46.54  tff(c_91, plain, (r1_tsep_1('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_68])).
% 57.25/46.54  tff(c_701, plain, (![B_143, A_144]: (r1_tsep_1(B_143, A_144) | ~r1_tsep_1(A_144, B_143) | ~l1_struct_0(B_143) | ~l1_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_141])).
% 57.25/46.54  tff(c_704, plain, (r1_tsep_1('#skF_9', '#skF_8') | ~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_91, c_701])).
% 57.25/46.54  tff(c_728, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_704])).
% 57.25/46.54  tff(c_731, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_54, c_728])).
% 57.25/46.54  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_731])).
% 57.25/46.54  tff(c_737, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_704])).
% 57.25/46.54  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 57.25/46.54  tff(c_34, plain, (![A_27]: (r1_xboole_0(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_88])).
% 57.25/46.54  tff(c_92, plain, (![B_60, A_61]: (r1_xboole_0(B_60, A_61) | ~r1_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 57.25/46.54  tff(c_95, plain, (![A_27]: (r1_xboole_0(k1_xboole_0, A_27))), inference(resolution, [status(thm)], [c_34, c_92])).
% 57.25/46.54  tff(c_32, plain, (![A_26]: (r1_tarski(k1_xboole_0, A_26))), inference(cnfTransformation, [status(thm)], [f_86])).
% 57.25/46.54  tff(c_159, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_84])).
% 57.25/46.54  tff(c_170, plain, (![A_26]: (k3_xboole_0(k1_xboole_0, A_26)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_159])).
% 57.25/46.54  tff(c_221, plain, (![A_87, B_88, C_89]: (~r1_xboole_0(A_87, B_88) | ~r2_hidden(C_89, k3_xboole_0(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 57.25/46.54  tff(c_231, plain, (![A_26, C_89]: (~r1_xboole_0(k1_xboole_0, A_26) | ~r2_hidden(C_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_170, c_221])).
% 57.25/46.54  tff(c_240, plain, (![C_90]: (~r2_hidden(C_90, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_231])).
% 57.25/46.54  tff(c_250, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_240])).
% 57.25/46.54  tff(c_130, plain, (l1_pre_topc('#skF_9') | ~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_72, c_124])).
% 57.25/46.54  tff(c_139, plain, (l1_pre_topc('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_130])).
% 57.25/46.54  tff(c_70, plain, (m1_pre_topc('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_176])).
% 57.25/46.54  tff(c_66, plain, (![B_49, A_47]: (m1_subset_1(u1_struct_0(B_49), k1_zfmisc_1(u1_struct_0(A_47))) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_148])).
% 57.25/46.54  tff(c_112, plain, (![C_66, A_67]: (r1_tarski(C_66, A_67) | ~r2_hidden(C_66, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 57.25/46.54  tff(c_753, plain, (![A_147]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_147)), A_147) | v1_xboole_0(k1_zfmisc_1(A_147)))), inference(resolution, [status(thm)], [c_4, c_112])).
% 57.25/46.54  tff(c_208, plain, (![B_85, A_86]: (B_85=A_86 | ~r1_tarski(B_85, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_80])).
% 57.25/46.54  tff(c_216, plain, (![A_26]: (k1_xboole_0=A_26 | ~r1_tarski(A_26, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_208])).
% 57.25/46.54  tff(c_767, plain, ('#skF_1'(k1_zfmisc_1(k1_xboole_0))=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_753, c_216])).
% 57.25/46.54  tff(c_771, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_767])).
% 57.25/46.54  tff(c_141, plain, (![C_72, A_73]: (r2_hidden(C_72, k1_zfmisc_1(A_73)) | ~r1_tarski(C_72, A_73))), inference(cnfTransformation, [status(thm)], [f_95])).
% 57.25/46.54  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 57.25/46.54  tff(c_149, plain, (![A_73, C_72]: (~v1_xboole_0(k1_zfmisc_1(A_73)) | ~r1_tarski(C_72, A_73))), inference(resolution, [status(thm)], [c_141, c_2])).
% 57.25/46.54  tff(c_840, plain, (![C_152]: (~r1_tarski(C_152, k1_xboole_0))), inference(resolution, [status(thm)], [c_771, c_149])).
% 57.25/46.54  tff(c_867, plain, $false, inference(resolution, [status(thm)], [c_32, c_840])).
% 57.25/46.54  tff(c_869, plain, (~v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_767])).
% 57.25/46.54  tff(c_380, plain, (![A_107, B_108]: (r2_hidden('#skF_2'(A_107, B_108), A_107) | r1_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_38])).
% 57.25/46.54  tff(c_36, plain, (![C_32, A_28]: (r1_tarski(C_32, A_28) | ~r2_hidden(C_32, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 57.25/46.54  tff(c_1638, plain, (![A_205, B_206]: (r1_tarski('#skF_2'(k1_zfmisc_1(A_205), B_206), A_205) | r1_tarski(k1_zfmisc_1(A_205), B_206))), inference(resolution, [status(thm)], [c_380, c_36])).
% 57.25/46.54  tff(c_1695, plain, (![B_209]: ('#skF_2'(k1_zfmisc_1(k1_xboole_0), B_209)=k1_xboole_0 | r1_tarski(k1_zfmisc_1(k1_xboole_0), B_209))), inference(resolution, [status(thm)], [c_1638, c_216])).
% 57.25/46.54  tff(c_481, plain, (![C_121, B_122, A_123]: (r2_hidden(C_121, B_122) | ~r2_hidden(C_121, A_123) | ~r1_tarski(A_123, B_122))), inference(cnfTransformation, [status(thm)], [f_38])).
% 57.25/46.54  tff(c_1045, plain, (![A_165, B_166]: (r2_hidden('#skF_1'(A_165), B_166) | ~r1_tarski(A_165, B_166) | v1_xboole_0(A_165))), inference(resolution, [status(thm)], [c_4, c_481])).
% 57.25/46.54  tff(c_1070, plain, (![B_166, A_165]: (~v1_xboole_0(B_166) | ~r1_tarski(A_165, B_166) | v1_xboole_0(A_165))), inference(resolution, [status(thm)], [c_1045, c_2])).
% 57.25/46.54  tff(c_1698, plain, (![B_209]: (~v1_xboole_0(B_209) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | '#skF_2'(k1_zfmisc_1(k1_xboole_0), B_209)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1695, c_1070])).
% 57.25/46.54  tff(c_1763, plain, (![B_212]: (~v1_xboole_0(B_212) | '#skF_2'(k1_zfmisc_1(k1_xboole_0), B_212)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_869, c_1698])).
% 57.25/46.54  tff(c_38, plain, (![C_32, A_28]: (r2_hidden(C_32, k1_zfmisc_1(A_28)) | ~r1_tarski(C_32, A_28))), inference(cnfTransformation, [status(thm)], [f_95])).
% 57.25/46.54  tff(c_369, plain, (![A_105, B_106]: (~r2_hidden('#skF_2'(A_105, B_106), B_106) | r1_tarski(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_38])).
% 57.25/46.54  tff(c_379, plain, (![A_105, A_28]: (r1_tarski(A_105, k1_zfmisc_1(A_28)) | ~r1_tarski('#skF_2'(A_105, k1_zfmisc_1(A_28)), A_28))), inference(resolution, [status(thm)], [c_38, c_369])).
% 57.25/46.54  tff(c_1770, plain, (![A_28]: (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_zfmisc_1(A_28)) | ~r1_tarski(k1_xboole_0, A_28) | ~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(superposition, [status(thm), theory('equality')], [c_1763, c_379])).
% 57.25/46.54  tff(c_1804, plain, (![A_213]: (r1_tarski(k1_zfmisc_1(k1_xboole_0), k1_zfmisc_1(A_213)) | ~v1_xboole_0(k1_zfmisc_1(A_213)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1770])).
% 57.25/46.54  tff(c_1807, plain, (![A_213]: (v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_zfmisc_1(A_213)))), inference(resolution, [status(thm)], [c_1804, c_1070])).
% 57.25/46.54  tff(c_1821, plain, (![A_213]: (~v1_xboole_0(k1_zfmisc_1(A_213)))), inference(negUnitSimplification, [status(thm)], [c_869, c_1807])).
% 57.25/46.54  tff(c_198, plain, (![A_83, B_84]: (r2_hidden(A_83, B_84) | v1_xboole_0(B_84) | ~m1_subset_1(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_105])).
% 57.25/46.54  tff(c_206, plain, (![A_83, A_28]: (r1_tarski(A_83, A_28) | v1_xboole_0(k1_zfmisc_1(A_28)) | ~m1_subset_1(A_83, k1_zfmisc_1(A_28)))), inference(resolution, [status(thm)], [c_198, c_36])).
% 57.25/46.54  tff(c_2759, plain, (![A_247, A_248]: (r1_tarski(A_247, A_248) | ~m1_subset_1(A_247, k1_zfmisc_1(A_248)))), inference(negUnitSimplification, [status(thm)], [c_1821, c_206])).
% 57.25/46.54  tff(c_2763, plain, (![B_49, A_47]: (r1_tarski(u1_struct_0(B_49), u1_struct_0(A_47)) | ~m1_pre_topc(B_49, A_47) | ~l1_pre_topc(A_47))), inference(resolution, [status(thm)], [c_66, c_2759])).
% 57.25/46.54  tff(c_736, plain, (~l1_struct_0('#skF_9') | r1_tsep_1('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_704])).
% 57.25/46.54  tff(c_738, plain, (~l1_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_736])).
% 57.25/46.54  tff(c_741, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_54, c_738])).
% 57.25/46.54  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_741])).
% 57.25/46.54  tff(c_747, plain, (l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_736])).
% 57.25/46.54  tff(c_16, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 57.25/46.54  tff(c_18, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 57.25/46.54  tff(c_498, plain, (![A_12, B_13, B_122]: (r2_hidden('#skF_3'(A_12, B_13), B_122) | ~r1_tarski(A_12, B_122) | r1_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_18, c_481])).
% 57.25/46.54  tff(c_907, plain, (![A_154, B_155]: (r1_xboole_0(u1_struct_0(A_154), u1_struct_0(B_155)) | ~r1_tsep_1(A_154, B_155) | ~l1_struct_0(B_155) | ~l1_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_133])).
% 57.25/46.54  tff(c_14, plain, (![A_12, B_13, C_16]: (~r1_xboole_0(A_12, B_13) | ~r2_hidden(C_16, B_13) | ~r2_hidden(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 57.25/46.54  tff(c_5918, plain, (![C_362, B_363, A_364]: (~r2_hidden(C_362, u1_struct_0(B_363)) | ~r2_hidden(C_362, u1_struct_0(A_364)) | ~r1_tsep_1(A_364, B_363) | ~l1_struct_0(B_363) | ~l1_struct_0(A_364))), inference(resolution, [status(thm)], [c_907, c_14])).
% 57.25/46.54  tff(c_73434, plain, (![A_1240, B_1241, A_1242, B_1243]: (~r2_hidden('#skF_3'(A_1240, B_1241), u1_struct_0(A_1242)) | ~r1_tsep_1(A_1242, B_1243) | ~l1_struct_0(B_1243) | ~l1_struct_0(A_1242) | ~r1_tarski(A_1240, u1_struct_0(B_1243)) | r1_xboole_0(A_1240, B_1241))), inference(resolution, [status(thm)], [c_498, c_5918])).
% 57.25/46.54  tff(c_255852, plain, (![A_2385, B_2386, A_2387]: (~r1_tsep_1(A_2385, B_2386) | ~l1_struct_0(B_2386) | ~l1_struct_0(A_2385) | ~r1_tarski(A_2387, u1_struct_0(B_2386)) | r1_xboole_0(A_2387, u1_struct_0(A_2385)))), inference(resolution, [status(thm)], [c_16, c_73434])).
% 57.25/46.54  tff(c_255856, plain, (![A_2387]: (~l1_struct_0('#skF_9') | ~l1_struct_0('#skF_8') | ~r1_tarski(A_2387, u1_struct_0('#skF_9')) | r1_xboole_0(A_2387, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_91, c_255852])).
% 57.25/46.54  tff(c_256185, plain, (![A_2389]: (~r1_tarski(A_2389, u1_struct_0('#skF_9')) | r1_xboole_0(A_2389, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_737, c_747, c_255856])).
% 57.25/46.54  tff(c_28, plain, (![B_23]: (r1_tarski(B_23, B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 57.25/46.54  tff(c_171, plain, (![B_23]: (k3_xboole_0(B_23, B_23)=B_23)), inference(resolution, [status(thm)], [c_28, c_159])).
% 57.25/46.54  tff(c_22, plain, (![A_17, B_18, C_21]: (~r1_xboole_0(A_17, B_18) | ~r2_hidden(C_21, k3_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 57.25/46.54  tff(c_671, plain, (![A_140, B_141, B_142]: (~r1_xboole_0(A_140, B_141) | r1_tarski(k3_xboole_0(A_140, B_141), B_142))), inference(resolution, [status(thm)], [c_380, c_22])).
% 57.25/46.54  tff(c_24, plain, (![B_23, A_22]: (B_23=A_22 | ~r1_tarski(B_23, A_22) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 57.25/46.54  tff(c_16833, plain, (![A_567, B_568, B_569]: (k3_xboole_0(A_567, B_568)=B_569 | ~r1_tarski(B_569, k3_xboole_0(A_567, B_568)) | ~r1_xboole_0(A_567, B_568))), inference(resolution, [status(thm)], [c_671, c_24])).
% 57.25/46.54  tff(c_16991, plain, (![B_23, B_569]: (k3_xboole_0(B_23, B_23)=B_569 | ~r1_tarski(B_569, B_23) | ~r1_xboole_0(B_23, B_23))), inference(superposition, [status(thm), theory('equality')], [c_171, c_16833])).
% 57.25/46.54  tff(c_17041, plain, (![B_571, B_570]: (B_571=B_570 | ~r1_tarski(B_570, B_571) | ~r1_xboole_0(B_571, B_571))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_16991])).
% 57.25/46.54  tff(c_17124, plain, (![A_26]: (k1_xboole_0=A_26 | ~r1_xboole_0(A_26, A_26))), inference(resolution, [status(thm)], [c_32, c_17041])).
% 57.25/46.54  tff(c_256476, plain, (u1_struct_0('#skF_8')=k1_xboole_0 | ~r1_tarski(u1_struct_0('#skF_8'), u1_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_256185, c_17124])).
% 57.25/46.54  tff(c_256508, plain, (~r1_tarski(u1_struct_0('#skF_8'), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_256476])).
% 57.25/46.54  tff(c_256521, plain, (~m1_pre_topc('#skF_8', '#skF_9') | ~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_2763, c_256508])).
% 57.25/46.54  tff(c_256528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_70, c_256521])).
% 57.25/46.54  tff(c_256529, plain, (u1_struct_0('#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_256476])).
% 57.25/46.54  tff(c_58, plain, (![A_41]: (~v1_xboole_0(u1_struct_0(A_41)) | ~l1_struct_0(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_124])).
% 57.25/46.54  tff(c_256657, plain, (~v1_xboole_0(k1_xboole_0) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_256529, c_58])).
% 57.25/46.54  tff(c_256754, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_250, c_256657])).
% 57.25/46.54  tff(c_256756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_256754])).
% 57.25/46.54  tff(c_256758, plain, (~r1_tsep_1('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_68])).
% 57.25/46.54  tff(c_256757, plain, (r1_tsep_1('#skF_9', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 57.25/46.54  tff(c_257385, plain, (![B_2470, A_2471]: (r1_tsep_1(B_2470, A_2471) | ~r1_tsep_1(A_2471, B_2470) | ~l1_struct_0(B_2470) | ~l1_struct_0(A_2471))), inference(cnfTransformation, [status(thm)], [f_141])).
% 57.25/46.54  tff(c_257387, plain, (r1_tsep_1('#skF_8', '#skF_9') | ~l1_struct_0('#skF_8') | ~l1_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_256757, c_257385])).
% 57.25/46.54  tff(c_257390, plain, (~l1_struct_0('#skF_8') | ~l1_struct_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_256758, c_257387])).
% 57.25/46.54  tff(c_257391, plain, (~l1_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_257390])).
% 57.25/46.54  tff(c_257394, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_54, c_257391])).
% 57.25/46.54  tff(c_257398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256789, c_257394])).
% 57.25/46.54  tff(c_257399, plain, (~l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_257390])).
% 57.25/46.54  tff(c_257403, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_54, c_257399])).
% 57.25/46.54  tff(c_257407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_256786, c_257403])).
% 57.25/46.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 57.25/46.54  
% 57.25/46.54  Inference rules
% 57.25/46.54  ----------------------
% 57.25/46.54  #Ref     : 0
% 57.25/46.54  #Sup     : 66067
% 57.25/46.54  #Fact    : 0
% 57.25/46.54  #Define  : 0
% 57.25/46.54  #Split   : 21
% 57.25/46.54  #Chain   : 0
% 57.25/46.54  #Close   : 0
% 57.25/46.54  
% 57.25/46.54  Ordering : KBO
% 57.25/46.54  
% 57.25/46.54  Simplification rules
% 57.25/46.54  ----------------------
% 57.25/46.54  #Subsume      : 27638
% 57.25/46.54  #Demod        : 33551
% 57.25/46.54  #Tautology    : 18250
% 57.25/46.54  #SimpNegUnit  : 3293
% 57.25/46.54  #BackRed      : 710
% 57.25/46.54  
% 57.25/46.54  #Partial instantiations: 0
% 57.25/46.54  #Strategies tried      : 1
% 57.25/46.54  
% 57.25/46.54  Timing (in seconds)
% 57.25/46.54  ----------------------
% 57.25/46.54  Preprocessing        : 0.34
% 57.25/46.54  Parsing              : 0.19
% 57.25/46.54  CNF conversion       : 0.03
% 57.25/46.54  Main loop            : 45.38
% 57.25/46.54  Inferencing          : 4.82
% 57.25/46.54  Reduction            : 9.84
% 57.25/46.54  Demodulation         : 6.29
% 57.25/46.54  BG Simplification    : 0.53
% 57.25/46.54  Subsumption          : 27.28
% 57.25/46.54  Abstraction          : 0.92
% 57.25/46.54  MUC search           : 0.00
% 57.25/46.54  Cooper               : 0.00
% 57.25/46.54  Total                : 45.81
% 57.25/46.55  Index Insertion      : 0.00
% 57.25/46.55  Index Deletion       : 0.00
% 57.25/46.55  Index Matching       : 0.00
% 57.25/46.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

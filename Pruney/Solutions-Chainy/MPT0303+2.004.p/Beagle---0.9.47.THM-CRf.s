%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:51 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 407 expanded)
%              Number of leaves         :   18 ( 137 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 900 expanded)
%              Number of equality atoms :   36 ( 194 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_34,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_392,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden('#skF_2'(A_79,B_80,C_81),B_80)
      | r2_hidden('#skF_3'(A_79,B_80,C_81),C_81)
      | k3_xboole_0(A_79,B_80) = C_81 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_484,plain,(
    ! [A_84,B_85] :
      ( r2_hidden('#skF_3'(A_84,B_85,B_85),B_85)
      | k3_xboole_0(A_84,B_85) = B_85 ) ),
    inference(resolution,[status(thm)],[c_392,c_20])).

tff(c_115,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( r2_hidden(k4_tarski(A_50,B_51),k2_zfmisc_1(C_52,D_53))
      | ~ r2_hidden(B_51,D_53)
      | ~ r2_hidden(A_50,C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    k2_zfmisc_1('#skF_5','#skF_5') = k2_zfmisc_1('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_89,plain,(
    ! [A_39,C_40,B_41,D_42] :
      ( r2_hidden(A_39,C_40)
      | ~ r2_hidden(k4_tarski(A_39,B_41),k2_zfmisc_1(C_40,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_92,plain,(
    ! [A_39,B_41] :
      ( r2_hidden(A_39,'#skF_5')
      | ~ r2_hidden(k4_tarski(A_39,B_41),k2_zfmisc_1('#skF_4','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_89])).

tff(c_135,plain,(
    ! [A_50,B_51] :
      ( r2_hidden(A_50,'#skF_5')
      | ~ r2_hidden(B_51,'#skF_4')
      | ~ r2_hidden(A_50,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_115,c_92])).

tff(c_140,plain,(
    ! [B_51] : ~ r2_hidden(B_51,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_152,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(k4_tarski(A_56,B_57),k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(B_57,'#skF_5')
      | ~ r2_hidden(A_56,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_115])).

tff(c_30,plain,(
    ! [B_15,D_17,A_14,C_16] :
      ( r2_hidden(B_15,D_17)
      | ~ r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    ! [B_57,A_56] :
      ( r2_hidden(B_57,'#skF_4')
      | ~ r2_hidden(B_57,'#skF_5')
      | ~ r2_hidden(A_56,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_152,c_30])).

tff(c_174,plain,(
    ! [B_57,A_56] :
      ( ~ r2_hidden(B_57,'#skF_5')
      | ~ r2_hidden(A_56,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_164])).

tff(c_204,plain,(
    ! [A_56] : ~ r2_hidden(A_56,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_508,plain,(
    ! [A_86] : k3_xboole_0(A_86,'#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_484,c_204])).

tff(c_141,plain,(
    ! [B_54] : ~ r2_hidden(B_54,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_147,plain,(
    ! [B_55] : r1_tarski('#skF_4',B_55) ),
    inference(resolution,[status(thm)],[c_6,c_141])).

tff(c_26,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_151,plain,(
    ! [B_55] : k3_xboole_0('#skF_4',B_55) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_147,c_26])).

tff(c_529,plain,(
    '#skF_5' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_151])).

tff(c_566,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_529])).

tff(c_570,plain,(
    ! [B_87] : ~ r2_hidden(B_87,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_576,plain,(
    ! [B_88] : r1_tarski('#skF_5',B_88) ),
    inference(resolution,[status(thm)],[c_6,c_570])).

tff(c_580,plain,(
    ! [B_88] : k3_xboole_0('#skF_5',B_88) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_576,c_26])).

tff(c_615,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_2'(A_92,B_93,C_94),A_92)
      | r2_hidden('#skF_3'(A_92,B_93,C_94),C_94)
      | k3_xboole_0(A_92,B_93) = C_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_567,plain,(
    ! [B_57] : ~ r2_hidden(B_57,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_619,plain,(
    ! [B_93,C_94] :
      ( r2_hidden('#skF_3'('#skF_5',B_93,C_94),C_94)
      | k3_xboole_0('#skF_5',B_93) = C_94 ) ),
    inference(resolution,[status(thm)],[c_615,c_567])).

tff(c_658,plain,(
    ! [B_95,C_96] :
      ( r2_hidden('#skF_3'('#skF_5',B_95,C_96),C_96)
      | C_96 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_619])).

tff(c_666,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_658,c_140])).

tff(c_682,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_666])).

tff(c_684,plain,(
    ! [A_97] :
      ( r2_hidden(A_97,'#skF_5')
      | ~ r2_hidden(A_97,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_713,plain,(
    ! [A_100] :
      ( r1_tarski(A_100,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_100,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_684,c_4])).

tff(c_718,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_713])).

tff(c_722,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_718,c_26])).

tff(c_1389,plain,(
    ! [A_153,B_154,C_155] :
      ( r2_hidden('#skF_2'(A_153,B_154,C_155),B_154)
      | r2_hidden('#skF_3'(A_153,B_154,C_155),C_155)
      | k3_xboole_0(A_153,B_154) = C_155 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1424,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_3'(A_153,B_154,B_154),B_154)
      | k3_xboole_0(A_153,B_154) = B_154 ) ),
    inference(resolution,[status(thm)],[c_1389,c_20])).

tff(c_3554,plain,(
    ! [A_245,B_246] :
      ( r2_hidden('#skF_3'(A_245,B_246,B_246),B_246)
      | k3_xboole_0(A_245,B_246) = B_246 ) ),
    inference(resolution,[status(thm)],[c_1389,c_20])).

tff(c_693,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(k4_tarski(A_98,B_99),k2_zfmisc_1('#skF_4','#skF_4'))
      | ~ r2_hidden(B_99,'#skF_5')
      | ~ r2_hidden(A_98,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_115])).

tff(c_32,plain,(
    ! [A_14,C_16,B_15,D_17] :
      ( r2_hidden(A_14,C_16)
      | ~ r2_hidden(k4_tarski(A_14,B_15),k2_zfmisc_1(C_16,D_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_710,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(A_98,'#skF_4')
      | ~ r2_hidden(B_99,'#skF_5')
      | ~ r2_hidden(A_98,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_693,c_32])).

tff(c_736,plain,(
    ! [B_99] : ~ r2_hidden(B_99,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_710])).

tff(c_683,plain,(
    ! [A_50] :
      ( r2_hidden(A_50,'#skF_5')
      | ~ r2_hidden(A_50,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_752,plain,(
    ! [A_105] : ~ r2_hidden(A_105,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_683])).

tff(c_764,plain,(
    ! [B_107] : r1_tarski('#skF_4',B_107) ),
    inference(resolution,[status(thm)],[c_6,c_752])).

tff(c_768,plain,(
    ! [B_107] : k3_xboole_0('#skF_4',B_107) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_764,c_26])).

tff(c_834,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_2'(A_112,B_113,C_114),A_112)
      | r2_hidden('#skF_3'(A_112,B_113,C_114),C_114)
      | k3_xboole_0(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_737,plain,(
    ! [A_50] : ~ r2_hidden(A_50,'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_736,c_683])).

tff(c_838,plain,(
    ! [B_113,C_114] :
      ( r2_hidden('#skF_3'('#skF_4',B_113,C_114),C_114)
      | k3_xboole_0('#skF_4',B_113) = C_114 ) ),
    inference(resolution,[status(thm)],[c_834,c_737])).

tff(c_882,plain,(
    ! [B_115,C_116] :
      ( r2_hidden('#skF_3'('#skF_4',B_115,C_116),C_116)
      | C_116 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_838])).

tff(c_890,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_882,c_736])).

tff(c_906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_890])).

tff(c_907,plain,(
    ! [A_98] :
      ( r2_hidden(A_98,'#skF_4')
      | ~ r2_hidden(A_98,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_710])).

tff(c_3583,plain,(
    ! [A_245] :
      ( r2_hidden('#skF_3'(A_245,'#skF_5','#skF_5'),'#skF_4')
      | k3_xboole_0(A_245,'#skF_5') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3554,c_907])).

tff(c_3594,plain,(
    ! [A_248,B_249,C_250] :
      ( r2_hidden('#skF_2'(A_248,B_249,C_250),B_249)
      | ~ r2_hidden('#skF_3'(A_248,B_249,C_250),B_249)
      | ~ r2_hidden('#skF_3'(A_248,B_249,C_250),A_248)
      | k3_xboole_0(A_248,B_249) = C_250 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3597,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3583,c_3594])).

tff(c_3614,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_3597])).

tff(c_3615,plain,
    ( r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3614])).

tff(c_3746,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3615])).

tff(c_3766,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1424,c_3746])).

tff(c_3773,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_3766])).

tff(c_3775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3773])).

tff(c_3777,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3615])).

tff(c_3813,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_3777,c_907])).

tff(c_3776,plain,(
    r2_hidden('#skF_2'('#skF_4','#skF_5','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3615])).

tff(c_3815,plain,(
    ! [A_259,B_260,C_261] :
      ( ~ r2_hidden('#skF_2'(A_259,B_260,C_261),C_261)
      | ~ r2_hidden('#skF_3'(A_259,B_260,C_261),B_260)
      | ~ r2_hidden('#skF_3'(A_259,B_260,C_261),A_259)
      | k3_xboole_0(A_259,B_260) = C_261 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3817,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4')
    | k3_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3776,c_3815])).

tff(c_3832,plain,
    ( ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_722,c_3777,c_3817])).

tff(c_3833,plain,(
    ~ r2_hidden('#skF_3'('#skF_4','#skF_5','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3832])).

tff(c_3858,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3813,c_3833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 21:02:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.71  
% 4.11/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.71  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.11/1.71  
% 4.11/1.71  %Foreground sorts:
% 4.11/1.71  
% 4.11/1.71  
% 4.11/1.71  %Background operators:
% 4.11/1.71  
% 4.11/1.71  
% 4.11/1.71  %Foreground operators:
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.11/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.11/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.11/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.11/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.11/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.11/1.71  
% 4.11/1.73  tff(f_56, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, A) = k2_zfmisc_1(B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 4.11/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.11/1.73  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.11/1.73  tff(f_51, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.11/1.73  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.11/1.73  tff(c_34, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.11/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.73  tff(c_392, plain, (![A_79, B_80, C_81]: (r2_hidden('#skF_2'(A_79, B_80, C_81), B_80) | r2_hidden('#skF_3'(A_79, B_80, C_81), C_81) | k3_xboole_0(A_79, B_80)=C_81)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.73  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.73  tff(c_484, plain, (![A_84, B_85]: (r2_hidden('#skF_3'(A_84, B_85, B_85), B_85) | k3_xboole_0(A_84, B_85)=B_85)), inference(resolution, [status(thm)], [c_392, c_20])).
% 4.11/1.73  tff(c_115, plain, (![A_50, B_51, C_52, D_53]: (r2_hidden(k4_tarski(A_50, B_51), k2_zfmisc_1(C_52, D_53)) | ~r2_hidden(B_51, D_53) | ~r2_hidden(A_50, C_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.11/1.73  tff(c_36, plain, (k2_zfmisc_1('#skF_5', '#skF_5')=k2_zfmisc_1('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.11/1.73  tff(c_89, plain, (![A_39, C_40, B_41, D_42]: (r2_hidden(A_39, C_40) | ~r2_hidden(k4_tarski(A_39, B_41), k2_zfmisc_1(C_40, D_42)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.11/1.73  tff(c_92, plain, (![A_39, B_41]: (r2_hidden(A_39, '#skF_5') | ~r2_hidden(k4_tarski(A_39, B_41), k2_zfmisc_1('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_36, c_89])).
% 4.11/1.73  tff(c_135, plain, (![A_50, B_51]: (r2_hidden(A_50, '#skF_5') | ~r2_hidden(B_51, '#skF_4') | ~r2_hidden(A_50, '#skF_4'))), inference(resolution, [status(thm)], [c_115, c_92])).
% 4.11/1.73  tff(c_140, plain, (![B_51]: (~r2_hidden(B_51, '#skF_4'))), inference(splitLeft, [status(thm)], [c_135])).
% 4.11/1.73  tff(c_152, plain, (![A_56, B_57]: (r2_hidden(k4_tarski(A_56, B_57), k2_zfmisc_1('#skF_4', '#skF_4')) | ~r2_hidden(B_57, '#skF_5') | ~r2_hidden(A_56, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_115])).
% 4.11/1.73  tff(c_30, plain, (![B_15, D_17, A_14, C_16]: (r2_hidden(B_15, D_17) | ~r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.11/1.73  tff(c_164, plain, (![B_57, A_56]: (r2_hidden(B_57, '#skF_4') | ~r2_hidden(B_57, '#skF_5') | ~r2_hidden(A_56, '#skF_5'))), inference(resolution, [status(thm)], [c_152, c_30])).
% 4.11/1.73  tff(c_174, plain, (![B_57, A_56]: (~r2_hidden(B_57, '#skF_5') | ~r2_hidden(A_56, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_140, c_164])).
% 4.11/1.73  tff(c_204, plain, (![A_56]: (~r2_hidden(A_56, '#skF_5'))), inference(splitLeft, [status(thm)], [c_174])).
% 4.11/1.73  tff(c_508, plain, (![A_86]: (k3_xboole_0(A_86, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_484, c_204])).
% 4.11/1.73  tff(c_141, plain, (![B_54]: (~r2_hidden(B_54, '#skF_4'))), inference(splitLeft, [status(thm)], [c_135])).
% 4.11/1.73  tff(c_147, plain, (![B_55]: (r1_tarski('#skF_4', B_55))), inference(resolution, [status(thm)], [c_6, c_141])).
% 4.11/1.73  tff(c_26, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.11/1.73  tff(c_151, plain, (![B_55]: (k3_xboole_0('#skF_4', B_55)='#skF_4')), inference(resolution, [status(thm)], [c_147, c_26])).
% 4.11/1.73  tff(c_529, plain, ('#skF_5'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_508, c_151])).
% 4.11/1.73  tff(c_566, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_529])).
% 4.11/1.73  tff(c_570, plain, (![B_87]: (~r2_hidden(B_87, '#skF_5'))), inference(splitRight, [status(thm)], [c_174])).
% 4.11/1.73  tff(c_576, plain, (![B_88]: (r1_tarski('#skF_5', B_88))), inference(resolution, [status(thm)], [c_6, c_570])).
% 4.11/1.73  tff(c_580, plain, (![B_88]: (k3_xboole_0('#skF_5', B_88)='#skF_5')), inference(resolution, [status(thm)], [c_576, c_26])).
% 4.11/1.73  tff(c_615, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_2'(A_92, B_93, C_94), A_92) | r2_hidden('#skF_3'(A_92, B_93, C_94), C_94) | k3_xboole_0(A_92, B_93)=C_94)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.73  tff(c_567, plain, (![B_57]: (~r2_hidden(B_57, '#skF_5'))), inference(splitRight, [status(thm)], [c_174])).
% 4.11/1.73  tff(c_619, plain, (![B_93, C_94]: (r2_hidden('#skF_3'('#skF_5', B_93, C_94), C_94) | k3_xboole_0('#skF_5', B_93)=C_94)), inference(resolution, [status(thm)], [c_615, c_567])).
% 4.11/1.73  tff(c_658, plain, (![B_95, C_96]: (r2_hidden('#skF_3'('#skF_5', B_95, C_96), C_96) | C_96='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_580, c_619])).
% 4.11/1.73  tff(c_666, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_658, c_140])).
% 4.11/1.73  tff(c_682, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_666])).
% 4.11/1.73  tff(c_684, plain, (![A_97]: (r2_hidden(A_97, '#skF_5') | ~r2_hidden(A_97, '#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 4.11/1.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.73  tff(c_713, plain, (![A_100]: (r1_tarski(A_100, '#skF_5') | ~r2_hidden('#skF_1'(A_100, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_684, c_4])).
% 4.11/1.73  tff(c_718, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_713])).
% 4.11/1.73  tff(c_722, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_718, c_26])).
% 4.11/1.73  tff(c_1389, plain, (![A_153, B_154, C_155]: (r2_hidden('#skF_2'(A_153, B_154, C_155), B_154) | r2_hidden('#skF_3'(A_153, B_154, C_155), C_155) | k3_xboole_0(A_153, B_154)=C_155)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.73  tff(c_1424, plain, (![A_153, B_154]: (r2_hidden('#skF_3'(A_153, B_154, B_154), B_154) | k3_xboole_0(A_153, B_154)=B_154)), inference(resolution, [status(thm)], [c_1389, c_20])).
% 4.11/1.73  tff(c_3554, plain, (![A_245, B_246]: (r2_hidden('#skF_3'(A_245, B_246, B_246), B_246) | k3_xboole_0(A_245, B_246)=B_246)), inference(resolution, [status(thm)], [c_1389, c_20])).
% 4.11/1.73  tff(c_693, plain, (![A_98, B_99]: (r2_hidden(k4_tarski(A_98, B_99), k2_zfmisc_1('#skF_4', '#skF_4')) | ~r2_hidden(B_99, '#skF_5') | ~r2_hidden(A_98, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_115])).
% 4.11/1.73  tff(c_32, plain, (![A_14, C_16, B_15, D_17]: (r2_hidden(A_14, C_16) | ~r2_hidden(k4_tarski(A_14, B_15), k2_zfmisc_1(C_16, D_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.11/1.73  tff(c_710, plain, (![A_98, B_99]: (r2_hidden(A_98, '#skF_4') | ~r2_hidden(B_99, '#skF_5') | ~r2_hidden(A_98, '#skF_5'))), inference(resolution, [status(thm)], [c_693, c_32])).
% 4.11/1.73  tff(c_736, plain, (![B_99]: (~r2_hidden(B_99, '#skF_5'))), inference(splitLeft, [status(thm)], [c_710])).
% 4.11/1.73  tff(c_683, plain, (![A_50]: (r2_hidden(A_50, '#skF_5') | ~r2_hidden(A_50, '#skF_4'))), inference(splitRight, [status(thm)], [c_135])).
% 4.11/1.73  tff(c_752, plain, (![A_105]: (~r2_hidden(A_105, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_736, c_683])).
% 4.11/1.73  tff(c_764, plain, (![B_107]: (r1_tarski('#skF_4', B_107))), inference(resolution, [status(thm)], [c_6, c_752])).
% 4.11/1.73  tff(c_768, plain, (![B_107]: (k3_xboole_0('#skF_4', B_107)='#skF_4')), inference(resolution, [status(thm)], [c_764, c_26])).
% 4.11/1.73  tff(c_834, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_2'(A_112, B_113, C_114), A_112) | r2_hidden('#skF_3'(A_112, B_113, C_114), C_114) | k3_xboole_0(A_112, B_113)=C_114)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.73  tff(c_737, plain, (![A_50]: (~r2_hidden(A_50, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_736, c_683])).
% 4.11/1.73  tff(c_838, plain, (![B_113, C_114]: (r2_hidden('#skF_3'('#skF_4', B_113, C_114), C_114) | k3_xboole_0('#skF_4', B_113)=C_114)), inference(resolution, [status(thm)], [c_834, c_737])).
% 4.11/1.73  tff(c_882, plain, (![B_115, C_116]: (r2_hidden('#skF_3'('#skF_4', B_115, C_116), C_116) | C_116='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_768, c_838])).
% 4.11/1.73  tff(c_890, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_882, c_736])).
% 4.11/1.73  tff(c_906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_890])).
% 4.11/1.73  tff(c_907, plain, (![A_98]: (r2_hidden(A_98, '#skF_4') | ~r2_hidden(A_98, '#skF_5'))), inference(splitRight, [status(thm)], [c_710])).
% 4.11/1.73  tff(c_3583, plain, (![A_245]: (r2_hidden('#skF_3'(A_245, '#skF_5', '#skF_5'), '#skF_4') | k3_xboole_0(A_245, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_3554, c_907])).
% 4.11/1.73  tff(c_3594, plain, (![A_248, B_249, C_250]: (r2_hidden('#skF_2'(A_248, B_249, C_250), B_249) | ~r2_hidden('#skF_3'(A_248, B_249, C_250), B_249) | ~r2_hidden('#skF_3'(A_248, B_249, C_250), A_248) | k3_xboole_0(A_248, B_249)=C_250)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.73  tff(c_3597, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3583, c_3594])).
% 4.11/1.73  tff(c_3614, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_722, c_3597])).
% 4.11/1.73  tff(c_3615, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_34, c_3614])).
% 4.11/1.73  tff(c_3746, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3615])).
% 4.11/1.73  tff(c_3766, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_1424, c_3746])).
% 4.11/1.73  tff(c_3773, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_722, c_3766])).
% 4.11/1.73  tff(c_3775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_3773])).
% 4.11/1.73  tff(c_3777, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_3615])).
% 4.11/1.73  tff(c_3813, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_3777, c_907])).
% 4.11/1.73  tff(c_3776, plain, (r2_hidden('#skF_2'('#skF_4', '#skF_5', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_3615])).
% 4.11/1.73  tff(c_3815, plain, (![A_259, B_260, C_261]: (~r2_hidden('#skF_2'(A_259, B_260, C_261), C_261) | ~r2_hidden('#skF_3'(A_259, B_260, C_261), B_260) | ~r2_hidden('#skF_3'(A_259, B_260, C_261), A_259) | k3_xboole_0(A_259, B_260)=C_261)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.11/1.73  tff(c_3817, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4') | k3_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_3776, c_3815])).
% 4.11/1.73  tff(c_3832, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_722, c_3777, c_3817])).
% 4.11/1.73  tff(c_3833, plain, (~r2_hidden('#skF_3'('#skF_4', '#skF_5', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_3832])).
% 4.11/1.73  tff(c_3858, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3813, c_3833])).
% 4.11/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.73  
% 4.11/1.73  Inference rules
% 4.11/1.73  ----------------------
% 4.11/1.73  #Ref     : 0
% 4.11/1.73  #Sup     : 824
% 4.11/1.73  #Fact    : 0
% 4.11/1.73  #Define  : 0
% 4.11/1.73  #Split   : 7
% 4.11/1.73  #Chain   : 0
% 4.11/1.73  #Close   : 0
% 4.11/1.73  
% 4.11/1.73  Ordering : KBO
% 4.11/1.73  
% 4.11/1.73  Simplification rules
% 4.11/1.73  ----------------------
% 4.11/1.73  #Subsume      : 141
% 4.11/1.73  #Demod        : 422
% 4.11/1.73  #Tautology    : 404
% 4.11/1.73  #SimpNegUnit  : 56
% 4.11/1.73  #BackRed      : 31
% 4.11/1.73  
% 4.11/1.73  #Partial instantiations: 0
% 4.11/1.73  #Strategies tried      : 1
% 4.11/1.73  
% 4.11/1.73  Timing (in seconds)
% 4.11/1.73  ----------------------
% 4.11/1.73  Preprocessing        : 0.28
% 4.11/1.73  Parsing              : 0.15
% 4.11/1.73  CNF conversion       : 0.02
% 4.11/1.73  Main loop            : 0.70
% 4.11/1.73  Inferencing          : 0.26
% 4.11/1.73  Reduction            : 0.20
% 4.11/1.73  Demodulation         : 0.13
% 4.11/1.73  BG Simplification    : 0.03
% 4.11/1.73  Subsumption          : 0.15
% 4.11/1.73  Abstraction          : 0.03
% 4.11/1.73  MUC search           : 0.00
% 4.11/1.73  Cooper               : 0.00
% 4.11/1.73  Total                : 1.02
% 4.11/1.73  Index Insertion      : 0.00
% 4.11/1.73  Index Deletion       : 0.00
% 4.11/1.73  Index Matching       : 0.00
% 4.11/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

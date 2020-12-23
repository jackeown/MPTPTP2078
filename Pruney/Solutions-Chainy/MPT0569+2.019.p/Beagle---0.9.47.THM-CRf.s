%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:38 EST 2020

% Result     : Theorem 38.29s
% Output     : CNFRefutation 38.29s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 117 expanded)
%              Number of leaves         :   34 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 200 expanded)
%              Number of equality atoms :   19 (  44 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_1 > #skF_9

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_66,plain,
    ( k10_relat_1('#skF_14','#skF_13') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_14'),'#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_105,plain,(
    r1_xboole_0(k2_relat_1('#skF_14'),'#skF_13') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_14'),'#skF_13')
    | k10_relat_1('#skF_14','#skF_13') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_173,plain,(
    k10_relat_1('#skF_14','#skF_13') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_60])).

tff(c_14,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_3'(A_13),A_13)
      | k1_xboole_0 = A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_80,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,k3_xboole_0(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    ! [A_94,B_95] :
      ( ~ r1_xboole_0(A_94,B_95)
      | k3_xboole_0(A_94,B_95) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_111,plain,(
    k3_xboole_0(k2_relat_1('#skF_14'),'#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_95])).

tff(c_460,plain,(
    ! [B_125,A_126] :
      ( k10_relat_1(B_125,k3_xboole_0(k2_relat_1(B_125),A_126)) = k10_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_473,plain,
    ( k10_relat_1('#skF_14',k1_xboole_0) = k10_relat_1('#skF_14','#skF_13')
    | ~ v1_relat_1('#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_460])).

tff(c_481,plain,(
    k10_relat_1('#skF_14',k1_xboole_0) = k10_relat_1('#skF_14','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_473])).

tff(c_622,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden('#skF_12'(A_136,B_137,C_138),B_137)
      | ~ r2_hidden(A_136,k10_relat_1(C_138,B_137))
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_96,plain,(
    ! [A_97,B_98] :
      ( ~ r1_xboole_0(A_97,B_98)
      | k3_xboole_0(A_97,B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_121,plain,(
    ! [A_99] : k3_xboole_0(A_99,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_12,plain,(
    ! [A_8,B_9,C_12] :
      ( ~ r1_xboole_0(A_8,B_9)
      | ~ r2_hidden(C_12,k3_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_126,plain,(
    ! [A_99,C_12] :
      ( ~ r1_xboole_0(A_99,k1_xboole_0)
      | ~ r2_hidden(C_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_12])).

tff(c_131,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_126])).

tff(c_643,plain,(
    ! [A_139,C_140] :
      ( ~ r2_hidden(A_139,k10_relat_1(C_140,k1_xboole_0))
      | ~ v1_relat_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_622,c_131])).

tff(c_658,plain,(
    ! [A_139] :
      ( ~ r2_hidden(A_139,k10_relat_1('#skF_14','#skF_13'))
      | ~ v1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_643])).

tff(c_679,plain,(
    ! [A_141] : ~ r2_hidden(A_141,k10_relat_1('#skF_14','#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_658])).

tff(c_703,plain,(
    k10_relat_1('#skF_14','#skF_13') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_679])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_703])).

tff(c_713,plain,(
    k10_relat_1('#skF_14','#skF_13') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_720,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_14'),'#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_60])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_721,plain,(
    ! [A_142] : k3_xboole_0(A_142,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_726,plain,(
    ! [A_142,C_12] :
      ( ~ r1_xboole_0(A_142,k1_xboole_0)
      | ~ r2_hidden(C_12,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_721,c_12])).

tff(c_731,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_726])).

tff(c_36,plain,(
    ! [A_58,C_73] :
      ( r2_hidden(k4_tarski('#skF_11'(A_58,k2_relat_1(A_58),C_73),C_73),A_58)
      | ~ r2_hidden(C_73,k2_relat_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1143,plain,(
    ! [D_186,A_187,B_188,E_189] :
      ( r2_hidden(D_186,k10_relat_1(A_187,B_188))
      | ~ r2_hidden(E_189,B_188)
      | ~ r2_hidden(k4_tarski(D_186,E_189),A_187)
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10686,plain,(
    ! [D_495,A_496,B_497,A_498] :
      ( r2_hidden(D_495,k10_relat_1(A_496,B_497))
      | ~ r2_hidden(k4_tarski(D_495,'#skF_1'(A_498,B_497)),A_496)
      | ~ v1_relat_1(A_496)
      | r1_xboole_0(A_498,B_497) ) ),
    inference(resolution,[status(thm)],[c_6,c_1143])).

tff(c_155856,plain,(
    ! [A_1678,A_1679,B_1680] :
      ( r2_hidden('#skF_11'(A_1678,k2_relat_1(A_1678),'#skF_1'(A_1679,B_1680)),k10_relat_1(A_1678,B_1680))
      | ~ v1_relat_1(A_1678)
      | r1_xboole_0(A_1679,B_1680)
      | ~ r2_hidden('#skF_1'(A_1679,B_1680),k2_relat_1(A_1678)) ) ),
    inference(resolution,[status(thm)],[c_36,c_10686])).

tff(c_156240,plain,(
    ! [A_1679] :
      ( r2_hidden('#skF_11'('#skF_14',k2_relat_1('#skF_14'),'#skF_1'(A_1679,'#skF_13')),k1_xboole_0)
      | ~ v1_relat_1('#skF_14')
      | r1_xboole_0(A_1679,'#skF_13')
      | ~ r2_hidden('#skF_1'(A_1679,'#skF_13'),k2_relat_1('#skF_14')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_713,c_155856])).

tff(c_156293,plain,(
    ! [A_1679] :
      ( r2_hidden('#skF_11'('#skF_14',k2_relat_1('#skF_14'),'#skF_1'(A_1679,'#skF_13')),k1_xboole_0)
      | r1_xboole_0(A_1679,'#skF_13')
      | ~ r2_hidden('#skF_1'(A_1679,'#skF_13'),k2_relat_1('#skF_14')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_156240])).

tff(c_156295,plain,(
    ! [A_1681] :
      ( r1_xboole_0(A_1681,'#skF_13')
      | ~ r2_hidden('#skF_1'(A_1681,'#skF_13'),k2_relat_1('#skF_14')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_731,c_156293])).

tff(c_156299,plain,(
    r1_xboole_0(k2_relat_1('#skF_14'),'#skF_13') ),
    inference(resolution,[status(thm)],[c_8,c_156295])).

tff(c_156303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_720,c_720,c_156299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:47:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 38.29/29.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.29/29.05  
% 38.29/29.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.29/29.05  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_12 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_10 > #skF_7 > #skF_8 > #skF_11 > #skF_3 > #skF_2 > #skF_1 > #skF_9
% 38.29/29.05  
% 38.29/29.05  %Foreground sorts:
% 38.29/29.05  
% 38.29/29.05  
% 38.29/29.05  %Background operators:
% 38.29/29.05  
% 38.29/29.05  
% 38.29/29.05  %Foreground operators:
% 38.29/29.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 38.29/29.05  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 38.29/29.05  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 38.29/29.05  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 38.29/29.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 38.29/29.05  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 38.29/29.05  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 38.29/29.05  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 38.29/29.05  tff('#skF_14', type, '#skF_14': $i).
% 38.29/29.05  tff('#skF_13', type, '#skF_13': $i).
% 38.29/29.05  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 38.29/29.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 38.29/29.05  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 38.29/29.05  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 38.29/29.05  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 38.29/29.05  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 38.29/29.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 38.29/29.05  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 38.29/29.05  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 38.29/29.05  tff('#skF_3', type, '#skF_3': $i > $i).
% 38.29/29.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 38.29/29.05  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 38.29/29.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 38.29/29.05  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 38.29/29.05  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 38.29/29.05  
% 38.29/29.07  tff(f_114, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 38.29/29.07  tff(f_69, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 38.29/29.07  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 38.29/29.07  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 38.29/29.07  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 38.29/29.07  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 38.29/29.07  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 38.29/29.07  tff(f_92, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 38.29/29.07  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 38.29/29.07  tff(c_66, plain, (k10_relat_1('#skF_14', '#skF_13')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_14'), '#skF_13')), inference(cnfTransformation, [status(thm)], [f_114])).
% 38.29/29.07  tff(c_105, plain, (r1_xboole_0(k2_relat_1('#skF_14'), '#skF_13')), inference(splitLeft, [status(thm)], [c_66])).
% 38.29/29.07  tff(c_60, plain, (~r1_xboole_0(k2_relat_1('#skF_14'), '#skF_13') | k10_relat_1('#skF_14', '#skF_13')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_114])).
% 38.29/29.07  tff(c_173, plain, (k10_relat_1('#skF_14', '#skF_13')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_60])).
% 38.29/29.07  tff(c_14, plain, (![A_13]: (r2_hidden('#skF_3'(A_13), A_13) | k1_xboole_0=A_13)), inference(cnfTransformation, [status(thm)], [f_69])).
% 38.29/29.07  tff(c_58, plain, (v1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_114])).
% 38.29/29.07  tff(c_80, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, k3_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 38.29/29.07  tff(c_95, plain, (![A_94, B_95]: (~r1_xboole_0(A_94, B_95) | k3_xboole_0(A_94, B_95)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_80])).
% 38.29/29.07  tff(c_111, plain, (k3_xboole_0(k2_relat_1('#skF_14'), '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_95])).
% 38.29/29.07  tff(c_460, plain, (![B_125, A_126]: (k10_relat_1(B_125, k3_xboole_0(k2_relat_1(B_125), A_126))=k10_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_107])).
% 38.29/29.07  tff(c_473, plain, (k10_relat_1('#skF_14', k1_xboole_0)=k10_relat_1('#skF_14', '#skF_13') | ~v1_relat_1('#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_111, c_460])).
% 38.29/29.07  tff(c_481, plain, (k10_relat_1('#skF_14', k1_xboole_0)=k10_relat_1('#skF_14', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_473])).
% 38.29/29.07  tff(c_622, plain, (![A_136, B_137, C_138]: (r2_hidden('#skF_12'(A_136, B_137, C_138), B_137) | ~r2_hidden(A_136, k10_relat_1(C_138, B_137)) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_103])).
% 38.29/29.07  tff(c_16, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 38.29/29.07  tff(c_96, plain, (![A_97, B_98]: (~r1_xboole_0(A_97, B_98) | k3_xboole_0(A_97, B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_80])).
% 38.29/29.07  tff(c_121, plain, (![A_99]: (k3_xboole_0(A_99, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_96])).
% 38.29/29.07  tff(c_12, plain, (![A_8, B_9, C_12]: (~r1_xboole_0(A_8, B_9) | ~r2_hidden(C_12, k3_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 38.29/29.07  tff(c_126, plain, (![A_99, C_12]: (~r1_xboole_0(A_99, k1_xboole_0) | ~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_121, c_12])).
% 38.29/29.07  tff(c_131, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_126])).
% 38.29/29.07  tff(c_643, plain, (![A_139, C_140]: (~r2_hidden(A_139, k10_relat_1(C_140, k1_xboole_0)) | ~v1_relat_1(C_140))), inference(resolution, [status(thm)], [c_622, c_131])).
% 38.29/29.07  tff(c_658, plain, (![A_139]: (~r2_hidden(A_139, k10_relat_1('#skF_14', '#skF_13')) | ~v1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_481, c_643])).
% 38.29/29.07  tff(c_679, plain, (![A_141]: (~r2_hidden(A_141, k10_relat_1('#skF_14', '#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_658])).
% 38.29/29.07  tff(c_703, plain, (k10_relat_1('#skF_14', '#skF_13')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_679])).
% 38.29/29.07  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_703])).
% 38.29/29.07  tff(c_713, plain, (k10_relat_1('#skF_14', '#skF_13')=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 38.29/29.07  tff(c_720, plain, (~r1_xboole_0(k2_relat_1('#skF_14'), '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_713, c_60])).
% 38.29/29.07  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.29/29.07  tff(c_721, plain, (![A_142]: (k3_xboole_0(A_142, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_96])).
% 38.29/29.07  tff(c_726, plain, (![A_142, C_12]: (~r1_xboole_0(A_142, k1_xboole_0) | ~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_721, c_12])).
% 38.29/29.07  tff(c_731, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_726])).
% 38.29/29.07  tff(c_36, plain, (![A_58, C_73]: (r2_hidden(k4_tarski('#skF_11'(A_58, k2_relat_1(A_58), C_73), C_73), A_58) | ~r2_hidden(C_73, k2_relat_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 38.29/29.07  tff(c_6, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 38.29/29.07  tff(c_1143, plain, (![D_186, A_187, B_188, E_189]: (r2_hidden(D_186, k10_relat_1(A_187, B_188)) | ~r2_hidden(E_189, B_188) | ~r2_hidden(k4_tarski(D_186, E_189), A_187) | ~v1_relat_1(A_187))), inference(cnfTransformation, [status(thm)], [f_84])).
% 38.29/29.07  tff(c_10686, plain, (![D_495, A_496, B_497, A_498]: (r2_hidden(D_495, k10_relat_1(A_496, B_497)) | ~r2_hidden(k4_tarski(D_495, '#skF_1'(A_498, B_497)), A_496) | ~v1_relat_1(A_496) | r1_xboole_0(A_498, B_497))), inference(resolution, [status(thm)], [c_6, c_1143])).
% 38.29/29.07  tff(c_155856, plain, (![A_1678, A_1679, B_1680]: (r2_hidden('#skF_11'(A_1678, k2_relat_1(A_1678), '#skF_1'(A_1679, B_1680)), k10_relat_1(A_1678, B_1680)) | ~v1_relat_1(A_1678) | r1_xboole_0(A_1679, B_1680) | ~r2_hidden('#skF_1'(A_1679, B_1680), k2_relat_1(A_1678)))), inference(resolution, [status(thm)], [c_36, c_10686])).
% 38.29/29.07  tff(c_156240, plain, (![A_1679]: (r2_hidden('#skF_11'('#skF_14', k2_relat_1('#skF_14'), '#skF_1'(A_1679, '#skF_13')), k1_xboole_0) | ~v1_relat_1('#skF_14') | r1_xboole_0(A_1679, '#skF_13') | ~r2_hidden('#skF_1'(A_1679, '#skF_13'), k2_relat_1('#skF_14')))), inference(superposition, [status(thm), theory('equality')], [c_713, c_155856])).
% 38.29/29.07  tff(c_156293, plain, (![A_1679]: (r2_hidden('#skF_11'('#skF_14', k2_relat_1('#skF_14'), '#skF_1'(A_1679, '#skF_13')), k1_xboole_0) | r1_xboole_0(A_1679, '#skF_13') | ~r2_hidden('#skF_1'(A_1679, '#skF_13'), k2_relat_1('#skF_14')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_156240])).
% 38.29/29.07  tff(c_156295, plain, (![A_1681]: (r1_xboole_0(A_1681, '#skF_13') | ~r2_hidden('#skF_1'(A_1681, '#skF_13'), k2_relat_1('#skF_14')))), inference(negUnitSimplification, [status(thm)], [c_731, c_156293])).
% 38.29/29.07  tff(c_156299, plain, (r1_xboole_0(k2_relat_1('#skF_14'), '#skF_13')), inference(resolution, [status(thm)], [c_8, c_156295])).
% 38.29/29.07  tff(c_156303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_720, c_720, c_156299])).
% 38.29/29.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.29/29.07  
% 38.29/29.07  Inference rules
% 38.29/29.07  ----------------------
% 38.29/29.07  #Ref     : 0
% 38.29/29.07  #Sup     : 41061
% 38.29/29.07  #Fact    : 0
% 38.29/29.07  #Define  : 0
% 38.29/29.07  #Split   : 21
% 38.29/29.07  #Chain   : 0
% 38.29/29.07  #Close   : 0
% 38.29/29.07  
% 38.29/29.07  Ordering : KBO
% 38.29/29.07  
% 38.29/29.07  Simplification rules
% 38.29/29.07  ----------------------
% 38.29/29.07  #Subsume      : 18243
% 38.29/29.07  #Demod        : 43232
% 38.29/29.07  #Tautology    : 15190
% 38.29/29.07  #SimpNegUnit  : 721
% 38.29/29.07  #BackRed      : 33
% 38.29/29.07  
% 38.29/29.07  #Partial instantiations: 0
% 38.29/29.07  #Strategies tried      : 1
% 38.29/29.07  
% 38.29/29.07  Timing (in seconds)
% 38.29/29.07  ----------------------
% 38.29/29.07  Preprocessing        : 0.33
% 38.29/29.07  Parsing              : 0.17
% 38.29/29.07  CNF conversion       : 0.03
% 38.29/29.07  Main loop            : 27.96
% 38.29/29.07  Inferencing          : 3.01
% 38.29/29.07  Reduction            : 3.75
% 38.29/29.07  Demodulation         : 2.58
% 38.29/29.07  BG Simplification    : 0.28
% 38.29/29.07  Subsumption          : 19.98
% 38.29/29.07  Abstraction          : 0.55
% 38.29/29.07  MUC search           : 0.00
% 38.29/29.07  Cooper               : 0.00
% 38.29/29.07  Total                : 28.32
% 38.29/29.07  Index Insertion      : 0.00
% 38.29/29.07  Index Deletion       : 0.00
% 38.29/29.07  Index Matching       : 0.00
% 38.29/29.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

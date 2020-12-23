%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:36 EST 2020

% Result     : Theorem 6.02s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 125 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 245 expanded)
%              Number of equality atoms :   20 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_46,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7')
    | k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_92,plain,(
    k10_relat_1('#skF_8','#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_247,plain,(
    ! [A_86,C_87] :
      ( r2_hidden(k4_tarski('#skF_5'(A_86,k2_relat_1(A_86),C_87),C_87),A_86)
      | ~ r2_hidden(C_87,k2_relat_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_77,plain,(
    ! [A_43,B_44] : ~ r2_hidden(A_43,k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_83,plain,(
    ! [A_11] : ~ r2_hidden(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_77])).

tff(c_272,plain,(
    ! [C_88] : ~ r2_hidden(C_88,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_247,c_83])).

tff(c_293,plain,(
    ! [A_89] : r1_xboole_0(A_89,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_272])).

tff(c_14,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_xboole_0 = A_8
      | ~ r1_xboole_0(B_9,C_10)
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_857,plain,(
    ! [A_147,A_148] :
      ( k1_xboole_0 = A_147
      | ~ r1_tarski(A_147,k2_relat_1(k1_xboole_0))
      | ~ r1_tarski(A_147,A_148) ) ),
    inference(resolution,[status(thm)],[c_293,c_14])).

tff(c_861,plain,(
    ! [A_148] :
      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(k1_xboole_0),A_148) ) ),
    inference(resolution,[status(thm)],[c_12,c_857])).

tff(c_953,plain,(
    ! [A_151] : ~ r1_tarski(k2_relat_1(k1_xboole_0),A_151) ),
    inference(splitLeft,[status(thm)],[c_861])).

tff(c_958,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_953])).

tff(c_959,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_861])).

tff(c_862,plain,(
    ! [A_149,B_150] :
      ( r2_hidden(k4_tarski('#skF_3'(A_149,B_150),'#skF_2'(A_149,B_150)),A_149)
      | r2_hidden('#skF_4'(A_149,B_150),B_150)
      | k2_relat_1(A_149) = B_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_951,plain,(
    ! [B_150] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_150),B_150)
      | k2_relat_1(k1_xboole_0) = B_150 ) ),
    inference(resolution,[status(thm)],[c_862,c_83])).

tff(c_1006,plain,(
    ! [B_153] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_153),B_153)
      | k1_xboole_0 = B_153 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_951])).

tff(c_44,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_34,B_35,C_36] :
      ( r2_hidden('#skF_6'(A_34,B_35,C_36),B_35)
      | ~ r2_hidden(A_34,k10_relat_1(C_36,B_35))
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_471,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden('#skF_6'(A_113,B_114,C_115),k2_relat_1(C_115))
      | ~ r2_hidden(A_113,k10_relat_1(C_115,B_114))
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_52,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_100,plain,(
    r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_52])).

tff(c_119,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [C_58] :
      ( ~ r2_hidden(C_58,'#skF_7')
      | ~ r2_hidden(C_58,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_100,c_119])).

tff(c_495,plain,(
    ! [A_113,B_114] :
      ( ~ r2_hidden('#skF_6'(A_113,B_114,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_113,k10_relat_1('#skF_8',B_114))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_471,c_127])).

tff(c_512,plain,(
    ! [A_118,B_119] :
      ( ~ r2_hidden('#skF_6'(A_118,B_119,'#skF_8'),'#skF_7')
      | ~ r2_hidden(A_118,k10_relat_1('#skF_8',B_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_495])).

tff(c_516,plain,(
    ! [A_34] :
      ( ~ r2_hidden(A_34,k10_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_512])).

tff(c_519,plain,(
    ! [A_34] : ~ r2_hidden(A_34,k10_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_516])).

tff(c_1026,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1006,c_519])).

tff(c_1054,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1026])).

tff(c_1055,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1056,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_24,plain,(
    ! [A_15,C_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_15,k2_relat_1(A_15),C_30),C_30),A_15)
      | ~ r2_hidden(C_30,k2_relat_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1554,plain,(
    ! [A_216,C_217,B_218,D_219] :
      ( r2_hidden(A_216,k10_relat_1(C_217,B_218))
      | ~ r2_hidden(D_219,B_218)
      | ~ r2_hidden(k4_tarski(A_216,D_219),C_217)
      | ~ r2_hidden(D_219,k2_relat_1(C_217))
      | ~ v1_relat_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2162,plain,(
    ! [A_262,C_263,B_264,A_265] :
      ( r2_hidden(A_262,k10_relat_1(C_263,B_264))
      | ~ r2_hidden(k4_tarski(A_262,'#skF_1'(A_265,B_264)),C_263)
      | ~ r2_hidden('#skF_1'(A_265,B_264),k2_relat_1(C_263))
      | ~ v1_relat_1(C_263)
      | r1_xboole_0(A_265,B_264) ) ),
    inference(resolution,[status(thm)],[c_4,c_1554])).

tff(c_5575,plain,(
    ! [A_433,A_434,B_435] :
      ( r2_hidden('#skF_5'(A_433,k2_relat_1(A_433),'#skF_1'(A_434,B_435)),k10_relat_1(A_433,B_435))
      | ~ v1_relat_1(A_433)
      | r1_xboole_0(A_434,B_435)
      | ~ r2_hidden('#skF_1'(A_434,B_435),k2_relat_1(A_433)) ) ),
    inference(resolution,[status(thm)],[c_24,c_2162])).

tff(c_5665,plain,(
    ! [A_434] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'(A_434,'#skF_7')),k1_xboole_0)
      | ~ v1_relat_1('#skF_8')
      | r1_xboole_0(A_434,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_434,'#skF_7'),k2_relat_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_5575])).

tff(c_5682,plain,(
    ! [A_434] :
      ( r2_hidden('#skF_5'('#skF_8',k2_relat_1('#skF_8'),'#skF_1'(A_434,'#skF_7')),k1_xboole_0)
      | r1_xboole_0(A_434,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_434,'#skF_7'),k2_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5665])).

tff(c_5684,plain,(
    ! [A_436] :
      ( r1_xboole_0(A_436,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_436,'#skF_7'),k2_relat_1('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_5682])).

tff(c_5688,plain,(
    r1_xboole_0(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_6,c_5684])).

tff(c_5692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1055,c_1055,c_5688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.02/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.22  
% 6.02/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.02/2.22  
% 6.02/2.22  %Foreground sorts:
% 6.02/2.22  
% 6.02/2.22  
% 6.02/2.22  %Background operators:
% 6.02/2.22  
% 6.02/2.22  
% 6.02/2.22  %Foreground operators:
% 6.02/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.02/2.22  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.02/2.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.02/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.02/2.22  tff('#skF_7', type, '#skF_7': $i).
% 6.02/2.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.02/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.02/2.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.02/2.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.02/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.02/2.22  tff('#skF_8', type, '#skF_8': $i).
% 6.02/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.22  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.02/2.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.02/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.02/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.02/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.02/2.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.02/2.22  
% 6.02/2.24  tff(f_92, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 6.02/2.24  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.02/2.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.02/2.24  tff(f_74, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 6.02/2.24  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.02/2.24  tff(f_66, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 6.02/2.24  tff(f_57, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 6.02/2.24  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 6.02/2.24  tff(c_46, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7') | k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.02/2.24  tff(c_92, plain, (k10_relat_1('#skF_8', '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 6.02/2.24  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.02/2.24  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.02/2.24  tff(c_247, plain, (![A_86, C_87]: (r2_hidden(k4_tarski('#skF_5'(A_86, k2_relat_1(A_86), C_87), C_87), A_86) | ~r2_hidden(C_87, k2_relat_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.02/2.24  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.02/2.24  tff(c_77, plain, (![A_43, B_44]: (~r2_hidden(A_43, k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.02/2.24  tff(c_83, plain, (![A_11]: (~r2_hidden(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_77])).
% 6.02/2.24  tff(c_272, plain, (![C_88]: (~r2_hidden(C_88, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_247, c_83])).
% 6.02/2.24  tff(c_293, plain, (![A_89]: (r1_xboole_0(A_89, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_272])).
% 6.02/2.24  tff(c_14, plain, (![A_8, B_9, C_10]: (k1_xboole_0=A_8 | ~r1_xboole_0(B_9, C_10) | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.02/2.24  tff(c_857, plain, (![A_147, A_148]: (k1_xboole_0=A_147 | ~r1_tarski(A_147, k2_relat_1(k1_xboole_0)) | ~r1_tarski(A_147, A_148))), inference(resolution, [status(thm)], [c_293, c_14])).
% 6.02/2.24  tff(c_861, plain, (![A_148]: (k2_relat_1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k2_relat_1(k1_xboole_0), A_148))), inference(resolution, [status(thm)], [c_12, c_857])).
% 6.02/2.24  tff(c_953, plain, (![A_151]: (~r1_tarski(k2_relat_1(k1_xboole_0), A_151))), inference(splitLeft, [status(thm)], [c_861])).
% 6.02/2.24  tff(c_958, plain, $false, inference(resolution, [status(thm)], [c_12, c_953])).
% 6.02/2.24  tff(c_959, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_861])).
% 6.02/2.24  tff(c_862, plain, (![A_149, B_150]: (r2_hidden(k4_tarski('#skF_3'(A_149, B_150), '#skF_2'(A_149, B_150)), A_149) | r2_hidden('#skF_4'(A_149, B_150), B_150) | k2_relat_1(A_149)=B_150)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.02/2.24  tff(c_951, plain, (![B_150]: (r2_hidden('#skF_4'(k1_xboole_0, B_150), B_150) | k2_relat_1(k1_xboole_0)=B_150)), inference(resolution, [status(thm)], [c_862, c_83])).
% 6.02/2.24  tff(c_1006, plain, (![B_153]: (r2_hidden('#skF_4'(k1_xboole_0, B_153), B_153) | k1_xboole_0=B_153)), inference(demodulation, [status(thm), theory('equality')], [c_959, c_951])).
% 6.02/2.24  tff(c_44, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.02/2.24  tff(c_38, plain, (![A_34, B_35, C_36]: (r2_hidden('#skF_6'(A_34, B_35, C_36), B_35) | ~r2_hidden(A_34, k10_relat_1(C_36, B_35)) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.02/2.24  tff(c_471, plain, (![A_113, B_114, C_115]: (r2_hidden('#skF_6'(A_113, B_114, C_115), k2_relat_1(C_115)) | ~r2_hidden(A_113, k10_relat_1(C_115, B_114)) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.02/2.24  tff(c_52, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.02/2.24  tff(c_100, plain, (r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_92, c_52])).
% 6.02/2.24  tff(c_119, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.02/2.24  tff(c_127, plain, (![C_58]: (~r2_hidden(C_58, '#skF_7') | ~r2_hidden(C_58, k2_relat_1('#skF_8')))), inference(resolution, [status(thm)], [c_100, c_119])).
% 6.02/2.24  tff(c_495, plain, (![A_113, B_114]: (~r2_hidden('#skF_6'(A_113, B_114, '#skF_8'), '#skF_7') | ~r2_hidden(A_113, k10_relat_1('#skF_8', B_114)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_471, c_127])).
% 6.02/2.24  tff(c_512, plain, (![A_118, B_119]: (~r2_hidden('#skF_6'(A_118, B_119, '#skF_8'), '#skF_7') | ~r2_hidden(A_118, k10_relat_1('#skF_8', B_119)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_495])).
% 6.02/2.24  tff(c_516, plain, (![A_34]: (~r2_hidden(A_34, k10_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_512])).
% 6.02/2.24  tff(c_519, plain, (![A_34]: (~r2_hidden(A_34, k10_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_516])).
% 6.02/2.24  tff(c_1026, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_1006, c_519])).
% 6.02/2.24  tff(c_1054, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1026])).
% 6.02/2.24  tff(c_1055, plain, (~r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 6.02/2.24  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.02/2.24  tff(c_1056, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 6.02/2.24  tff(c_24, plain, (![A_15, C_30]: (r2_hidden(k4_tarski('#skF_5'(A_15, k2_relat_1(A_15), C_30), C_30), A_15) | ~r2_hidden(C_30, k2_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.02/2.24  tff(c_1554, plain, (![A_216, C_217, B_218, D_219]: (r2_hidden(A_216, k10_relat_1(C_217, B_218)) | ~r2_hidden(D_219, B_218) | ~r2_hidden(k4_tarski(A_216, D_219), C_217) | ~r2_hidden(D_219, k2_relat_1(C_217)) | ~v1_relat_1(C_217))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.02/2.24  tff(c_2162, plain, (![A_262, C_263, B_264, A_265]: (r2_hidden(A_262, k10_relat_1(C_263, B_264)) | ~r2_hidden(k4_tarski(A_262, '#skF_1'(A_265, B_264)), C_263) | ~r2_hidden('#skF_1'(A_265, B_264), k2_relat_1(C_263)) | ~v1_relat_1(C_263) | r1_xboole_0(A_265, B_264))), inference(resolution, [status(thm)], [c_4, c_1554])).
% 6.02/2.24  tff(c_5575, plain, (![A_433, A_434, B_435]: (r2_hidden('#skF_5'(A_433, k2_relat_1(A_433), '#skF_1'(A_434, B_435)), k10_relat_1(A_433, B_435)) | ~v1_relat_1(A_433) | r1_xboole_0(A_434, B_435) | ~r2_hidden('#skF_1'(A_434, B_435), k2_relat_1(A_433)))), inference(resolution, [status(thm)], [c_24, c_2162])).
% 6.02/2.24  tff(c_5665, plain, (![A_434]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'(A_434, '#skF_7')), k1_xboole_0) | ~v1_relat_1('#skF_8') | r1_xboole_0(A_434, '#skF_7') | ~r2_hidden('#skF_1'(A_434, '#skF_7'), k2_relat_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_1056, c_5575])).
% 6.02/2.24  tff(c_5682, plain, (![A_434]: (r2_hidden('#skF_5'('#skF_8', k2_relat_1('#skF_8'), '#skF_1'(A_434, '#skF_7')), k1_xboole_0) | r1_xboole_0(A_434, '#skF_7') | ~r2_hidden('#skF_1'(A_434, '#skF_7'), k2_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5665])).
% 6.02/2.24  tff(c_5684, plain, (![A_436]: (r1_xboole_0(A_436, '#skF_7') | ~r2_hidden('#skF_1'(A_436, '#skF_7'), k2_relat_1('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_83, c_5682])).
% 6.02/2.24  tff(c_5688, plain, (r1_xboole_0(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_6, c_5684])).
% 6.02/2.24  tff(c_5692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1055, c_1055, c_5688])).
% 6.02/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.02/2.24  
% 6.02/2.24  Inference rules
% 6.02/2.24  ----------------------
% 6.02/2.24  #Ref     : 0
% 6.02/2.24  #Sup     : 1327
% 6.02/2.24  #Fact    : 0
% 6.02/2.24  #Define  : 0
% 6.02/2.24  #Split   : 7
% 6.02/2.24  #Chain   : 0
% 6.02/2.24  #Close   : 0
% 6.02/2.24  
% 6.02/2.24  Ordering : KBO
% 6.02/2.24  
% 6.02/2.24  Simplification rules
% 6.02/2.24  ----------------------
% 6.02/2.24  #Subsume      : 576
% 6.02/2.24  #Demod        : 793
% 6.02/2.24  #Tautology    : 246
% 6.02/2.24  #SimpNegUnit  : 45
% 6.02/2.24  #BackRed      : 36
% 6.02/2.24  
% 6.02/2.24  #Partial instantiations: 0
% 6.02/2.24  #Strategies tried      : 1
% 6.02/2.24  
% 6.02/2.24  Timing (in seconds)
% 6.02/2.24  ----------------------
% 6.26/2.24  Preprocessing        : 0.29
% 6.26/2.24  Parsing              : 0.15
% 6.26/2.24  CNF conversion       : 0.02
% 6.26/2.24  Main loop            : 1.18
% 6.26/2.24  Inferencing          : 0.36
% 6.26/2.24  Reduction            : 0.28
% 6.26/2.24  Demodulation         : 0.20
% 6.26/2.24  BG Simplification    : 0.04
% 6.26/2.24  Subsumption          : 0.42
% 6.26/2.24  Abstraction          : 0.05
% 6.26/2.24  MUC search           : 0.00
% 6.26/2.24  Cooper               : 0.00
% 6.26/2.24  Total                : 1.51
% 6.26/2.24  Index Insertion      : 0.00
% 6.26/2.24  Index Deletion       : 0.00
% 6.26/2.24  Index Matching       : 0.00
% 6.26/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

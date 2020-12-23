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
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 5.86s
% Output     : CNFRefutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 115 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  115 ( 216 expanded)
%              Number of equality atoms :   12 (  26 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_11 > #skF_6 > #skF_3 > #skF_5 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_83,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_62,plain,(
    ! [A_58] : v1_relat_1(k1_wellord2(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [C_56,D_57,A_50] :
      ( r2_hidden(k4_tarski(C_56,D_57),k1_wellord2(A_50))
      | ~ r1_tarski(C_56,D_57)
      | ~ r2_hidden(D_57,A_50)
      | ~ r2_hidden(C_56,A_50)
      | ~ v1_relat_1(k1_wellord2(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_420,plain,(
    ! [C_126,D_127,A_128] :
      ( r2_hidden(k4_tarski(C_126,D_127),k1_wellord2(A_128))
      | ~ r1_tarski(C_126,D_127)
      | ~ r2_hidden(D_127,A_128)
      | ~ r2_hidden(C_126,A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58])).

tff(c_16,plain,(
    ! [C_23,A_8,D_26] :
      ( r2_hidden(C_23,k1_relat_1(A_8))
      | ~ r2_hidden(k4_tarski(C_23,D_26),A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2964,plain,(
    ! [C_260,A_261,D_262] :
      ( r2_hidden(C_260,k1_relat_1(k1_wellord2(A_261)))
      | ~ r1_tarski(C_260,D_262)
      | ~ r2_hidden(D_262,A_261)
      | ~ r2_hidden(C_260,A_261) ) ),
    inference(resolution,[status(thm)],[c_420,c_16])).

tff(c_3082,plain,(
    ! [B_263,A_264] :
      ( r2_hidden(B_263,k1_relat_1(k1_wellord2(A_264)))
      | ~ r2_hidden(B_263,A_264) ) ),
    inference(resolution,[status(thm)],[c_12,c_2964])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3569,plain,(
    ! [A_279,A_280] :
      ( r1_tarski(A_279,k1_relat_1(k1_wellord2(A_280)))
      | ~ r2_hidden('#skF_1'(A_279,k1_relat_1(k1_wellord2(A_280))),A_280) ) ),
    inference(resolution,[status(thm)],[c_3082,c_4])).

tff(c_3635,plain,(
    ! [A_1] : r1_tarski(A_1,k1_relat_1(k1_wellord2(A_1))) ),
    inference(resolution,[status(thm)],[c_6,c_3569])).

tff(c_56,plain,(
    ! [A_50] :
      ( k3_relat_1(k1_wellord2(A_50)) = A_50
      | ~ v1_relat_1(k1_wellord2(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_70,plain,(
    ! [A_50] : k3_relat_1(k1_wellord2(A_50)) = A_50 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56])).

tff(c_133,plain,(
    ! [C_88,A_89] :
      ( r2_hidden(k4_tarski(C_88,'#skF_5'(A_89,k1_relat_1(A_89),C_88)),A_89)
      | ~ r2_hidden(C_88,k1_relat_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    ! [A_47,C_49,B_48] :
      ( r2_hidden(A_47,k3_relat_1(C_49))
      | ~ r2_hidden(k4_tarski(A_47,B_48),C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_153,plain,(
    ! [C_90,A_91] :
      ( r2_hidden(C_90,k3_relat_1(A_91))
      | ~ v1_relat_1(A_91)
      | ~ r2_hidden(C_90,k1_relat_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_133,c_42])).

tff(c_178,plain,(
    ! [C_90,A_50] :
      ( r2_hidden(C_90,A_50)
      | ~ v1_relat_1(k1_wellord2(A_50))
      | ~ r2_hidden(C_90,k1_relat_1(k1_wellord2(A_50))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_153])).

tff(c_187,plain,(
    ! [C_92,A_93] :
      ( r2_hidden(C_92,A_93)
      | ~ r2_hidden(C_92,k1_relat_1(k1_wellord2(A_93))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_178])).

tff(c_213,plain,(
    ! [A_98,B_99] :
      ( r2_hidden('#skF_1'(k1_relat_1(k1_wellord2(A_98)),B_99),A_98)
      | r1_tarski(k1_relat_1(k1_wellord2(A_98)),B_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_187])).

tff(c_227,plain,(
    ! [A_100] : r1_tarski(k1_relat_1(k1_wellord2(A_100)),A_100) ),
    inference(resolution,[status(thm)],[c_213,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_230,plain,(
    ! [A_100] :
      ( k1_relat_1(k1_wellord2(A_100)) = A_100
      | ~ r1_tarski(A_100,k1_relat_1(k1_wellord2(A_100))) ) ),
    inference(resolution,[status(thm)],[c_227,c_8])).

tff(c_3637,plain,(
    ! [A_100] : k1_relat_1(k1_wellord2(A_100)) = A_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3635,c_230])).

tff(c_28,plain,(
    ! [C_42,A_27,D_45] :
      ( r2_hidden(C_42,k2_relat_1(A_27))
      | ~ r2_hidden(k4_tarski(D_45,C_42),A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3956,plain,(
    ! [D_288,A_289,C_290] :
      ( r2_hidden(D_288,k2_relat_1(k1_wellord2(A_289)))
      | ~ r1_tarski(C_290,D_288)
      | ~ r2_hidden(D_288,A_289)
      | ~ r2_hidden(C_290,A_289) ) ),
    inference(resolution,[status(thm)],[c_420,c_28])).

tff(c_3996,plain,(
    ! [B_291,A_292] :
      ( r2_hidden(B_291,k2_relat_1(k1_wellord2(A_292)))
      | ~ r2_hidden(B_291,A_292) ) ),
    inference(resolution,[status(thm)],[c_12,c_3956])).

tff(c_4400,plain,(
    ! [A_306,A_307] :
      ( r1_tarski(A_306,k2_relat_1(k1_wellord2(A_307)))
      | ~ r2_hidden('#skF_1'(A_306,k2_relat_1(k1_wellord2(A_307))),A_307) ) ),
    inference(resolution,[status(thm)],[c_3996,c_4])).

tff(c_4461,plain,(
    ! [A_1] : r1_tarski(A_1,k2_relat_1(k1_wellord2(A_1))) ),
    inference(resolution,[status(thm)],[c_6,c_4400])).

tff(c_252,plain,(
    ! [A_105,C_106] :
      ( r2_hidden(k4_tarski('#skF_9'(A_105,k2_relat_1(A_105),C_106),C_106),A_105)
      | ~ r2_hidden(C_106,k2_relat_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_40,plain,(
    ! [B_48,C_49,A_47] :
      ( r2_hidden(B_48,k3_relat_1(C_49))
      | ~ r2_hidden(k4_tarski(A_47,B_48),C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_277,plain,(
    ! [C_107,A_108] :
      ( r2_hidden(C_107,k3_relat_1(A_108))
      | ~ v1_relat_1(A_108)
      | ~ r2_hidden(C_107,k2_relat_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_252,c_40])).

tff(c_310,plain,(
    ! [C_107,A_50] :
      ( r2_hidden(C_107,A_50)
      | ~ v1_relat_1(k1_wellord2(A_50))
      | ~ r2_hidden(C_107,k2_relat_1(k1_wellord2(A_50))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_277])).

tff(c_321,plain,(
    ! [C_109,A_110] :
      ( r2_hidden(C_109,A_110)
      | ~ r2_hidden(C_109,k2_relat_1(k1_wellord2(A_110))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_310])).

tff(c_370,plain,(
    ! [A_116,B_117] :
      ( r2_hidden('#skF_1'(k2_relat_1(k1_wellord2(A_116)),B_117),A_116)
      | r1_tarski(k2_relat_1(k1_wellord2(A_116)),B_117) ) ),
    inference(resolution,[status(thm)],[c_6,c_321])).

tff(c_389,plain,(
    ! [A_118] : r1_tarski(k2_relat_1(k1_wellord2(A_118)),A_118) ),
    inference(resolution,[status(thm)],[c_370,c_4])).

tff(c_392,plain,(
    ! [A_118] :
      ( k2_relat_1(k1_wellord2(A_118)) = A_118
      | ~ r1_tarski(A_118,k2_relat_1(k1_wellord2(A_118))) ) ),
    inference(resolution,[status(thm)],[c_389,c_8])).

tff(c_4534,plain,(
    ! [A_309] : k2_relat_1(k1_wellord2(A_309)) = A_309 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4461,c_392])).

tff(c_38,plain,(
    ! [A_46] :
      ( r1_tarski(A_46,k2_zfmisc_1(k1_relat_1(A_46),k2_relat_1(A_46)))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4570,plain,(
    ! [A_309] :
      ( r1_tarski(k1_wellord2(A_309),k2_zfmisc_1(k1_relat_1(k1_wellord2(A_309)),A_309))
      | ~ v1_relat_1(k1_wellord2(A_309)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4534,c_38])).

tff(c_4592,plain,(
    ! [A_309] : r1_tarski(k1_wellord2(A_309),k2_zfmisc_1(A_309,A_309)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3637,c_4570])).

tff(c_64,plain,(
    ~ r1_tarski(k1_wellord2('#skF_12'),k2_zfmisc_1('#skF_12','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4618,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4592,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.86/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.12  
% 5.86/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.86/2.12  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_11 > #skF_6 > #skF_3 > #skF_5 > #skF_10 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_12 > #skF_4
% 5.86/2.12  
% 5.86/2.12  %Foreground sorts:
% 5.86/2.12  
% 5.86/2.12  
% 5.86/2.12  %Background operators:
% 5.86/2.12  
% 5.86/2.12  
% 5.86/2.12  %Foreground operators:
% 5.86/2.12  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 5.86/2.12  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.86/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.86/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.86/2.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.86/2.12  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 5.86/2.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.86/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.86/2.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.86/2.12  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 5.86/2.12  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.86/2.12  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 5.86/2.12  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.86/2.12  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 5.86/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.86/2.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.86/2.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.86/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.86/2.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.86/2.12  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.86/2.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.86/2.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.86/2.12  tff('#skF_12', type, '#skF_12': $i).
% 5.86/2.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.86/2.12  
% 6.13/2.13  tff(f_83, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 6.13/2.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.13/2.13  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.13/2.13  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 6.13/2.13  tff(f_46, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 6.13/2.13  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 6.13/2.13  tff(f_54, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 6.13/2.13  tff(f_58, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 6.13/2.13  tff(f_86, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 6.13/2.13  tff(c_62, plain, (![A_58]: (v1_relat_1(k1_wellord2(A_58)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.13/2.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.13/2.13  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.13/2.13  tff(c_58, plain, (![C_56, D_57, A_50]: (r2_hidden(k4_tarski(C_56, D_57), k1_wellord2(A_50)) | ~r1_tarski(C_56, D_57) | ~r2_hidden(D_57, A_50) | ~r2_hidden(C_56, A_50) | ~v1_relat_1(k1_wellord2(A_50)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.13/2.13  tff(c_420, plain, (![C_126, D_127, A_128]: (r2_hidden(k4_tarski(C_126, D_127), k1_wellord2(A_128)) | ~r1_tarski(C_126, D_127) | ~r2_hidden(D_127, A_128) | ~r2_hidden(C_126, A_128))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58])).
% 6.13/2.13  tff(c_16, plain, (![C_23, A_8, D_26]: (r2_hidden(C_23, k1_relat_1(A_8)) | ~r2_hidden(k4_tarski(C_23, D_26), A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.13/2.13  tff(c_2964, plain, (![C_260, A_261, D_262]: (r2_hidden(C_260, k1_relat_1(k1_wellord2(A_261))) | ~r1_tarski(C_260, D_262) | ~r2_hidden(D_262, A_261) | ~r2_hidden(C_260, A_261))), inference(resolution, [status(thm)], [c_420, c_16])).
% 6.13/2.13  tff(c_3082, plain, (![B_263, A_264]: (r2_hidden(B_263, k1_relat_1(k1_wellord2(A_264))) | ~r2_hidden(B_263, A_264))), inference(resolution, [status(thm)], [c_12, c_2964])).
% 6.13/2.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.13/2.13  tff(c_3569, plain, (![A_279, A_280]: (r1_tarski(A_279, k1_relat_1(k1_wellord2(A_280))) | ~r2_hidden('#skF_1'(A_279, k1_relat_1(k1_wellord2(A_280))), A_280))), inference(resolution, [status(thm)], [c_3082, c_4])).
% 6.13/2.13  tff(c_3635, plain, (![A_1]: (r1_tarski(A_1, k1_relat_1(k1_wellord2(A_1))))), inference(resolution, [status(thm)], [c_6, c_3569])).
% 6.13/2.13  tff(c_56, plain, (![A_50]: (k3_relat_1(k1_wellord2(A_50))=A_50 | ~v1_relat_1(k1_wellord2(A_50)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.13/2.13  tff(c_70, plain, (![A_50]: (k3_relat_1(k1_wellord2(A_50))=A_50)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56])).
% 6.13/2.13  tff(c_133, plain, (![C_88, A_89]: (r2_hidden(k4_tarski(C_88, '#skF_5'(A_89, k1_relat_1(A_89), C_88)), A_89) | ~r2_hidden(C_88, k1_relat_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.13/2.13  tff(c_42, plain, (![A_47, C_49, B_48]: (r2_hidden(A_47, k3_relat_1(C_49)) | ~r2_hidden(k4_tarski(A_47, B_48), C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.13/2.13  tff(c_153, plain, (![C_90, A_91]: (r2_hidden(C_90, k3_relat_1(A_91)) | ~v1_relat_1(A_91) | ~r2_hidden(C_90, k1_relat_1(A_91)))), inference(resolution, [status(thm)], [c_133, c_42])).
% 6.13/2.13  tff(c_178, plain, (![C_90, A_50]: (r2_hidden(C_90, A_50) | ~v1_relat_1(k1_wellord2(A_50)) | ~r2_hidden(C_90, k1_relat_1(k1_wellord2(A_50))))), inference(superposition, [status(thm), theory('equality')], [c_70, c_153])).
% 6.13/2.13  tff(c_187, plain, (![C_92, A_93]: (r2_hidden(C_92, A_93) | ~r2_hidden(C_92, k1_relat_1(k1_wellord2(A_93))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_178])).
% 6.13/2.13  tff(c_213, plain, (![A_98, B_99]: (r2_hidden('#skF_1'(k1_relat_1(k1_wellord2(A_98)), B_99), A_98) | r1_tarski(k1_relat_1(k1_wellord2(A_98)), B_99))), inference(resolution, [status(thm)], [c_6, c_187])).
% 6.13/2.13  tff(c_227, plain, (![A_100]: (r1_tarski(k1_relat_1(k1_wellord2(A_100)), A_100))), inference(resolution, [status(thm)], [c_213, c_4])).
% 6.13/2.13  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.13/2.13  tff(c_230, plain, (![A_100]: (k1_relat_1(k1_wellord2(A_100))=A_100 | ~r1_tarski(A_100, k1_relat_1(k1_wellord2(A_100))))), inference(resolution, [status(thm)], [c_227, c_8])).
% 6.13/2.13  tff(c_3637, plain, (![A_100]: (k1_relat_1(k1_wellord2(A_100))=A_100)), inference(demodulation, [status(thm), theory('equality')], [c_3635, c_230])).
% 6.13/2.13  tff(c_28, plain, (![C_42, A_27, D_45]: (r2_hidden(C_42, k2_relat_1(A_27)) | ~r2_hidden(k4_tarski(D_45, C_42), A_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.13/2.13  tff(c_3956, plain, (![D_288, A_289, C_290]: (r2_hidden(D_288, k2_relat_1(k1_wellord2(A_289))) | ~r1_tarski(C_290, D_288) | ~r2_hidden(D_288, A_289) | ~r2_hidden(C_290, A_289))), inference(resolution, [status(thm)], [c_420, c_28])).
% 6.13/2.13  tff(c_3996, plain, (![B_291, A_292]: (r2_hidden(B_291, k2_relat_1(k1_wellord2(A_292))) | ~r2_hidden(B_291, A_292))), inference(resolution, [status(thm)], [c_12, c_3956])).
% 6.13/2.13  tff(c_4400, plain, (![A_306, A_307]: (r1_tarski(A_306, k2_relat_1(k1_wellord2(A_307))) | ~r2_hidden('#skF_1'(A_306, k2_relat_1(k1_wellord2(A_307))), A_307))), inference(resolution, [status(thm)], [c_3996, c_4])).
% 6.13/2.13  tff(c_4461, plain, (![A_1]: (r1_tarski(A_1, k2_relat_1(k1_wellord2(A_1))))), inference(resolution, [status(thm)], [c_6, c_4400])).
% 6.13/2.13  tff(c_252, plain, (![A_105, C_106]: (r2_hidden(k4_tarski('#skF_9'(A_105, k2_relat_1(A_105), C_106), C_106), A_105) | ~r2_hidden(C_106, k2_relat_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.13/2.13  tff(c_40, plain, (![B_48, C_49, A_47]: (r2_hidden(B_48, k3_relat_1(C_49)) | ~r2_hidden(k4_tarski(A_47, B_48), C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.13/2.13  tff(c_277, plain, (![C_107, A_108]: (r2_hidden(C_107, k3_relat_1(A_108)) | ~v1_relat_1(A_108) | ~r2_hidden(C_107, k2_relat_1(A_108)))), inference(resolution, [status(thm)], [c_252, c_40])).
% 6.13/2.13  tff(c_310, plain, (![C_107, A_50]: (r2_hidden(C_107, A_50) | ~v1_relat_1(k1_wellord2(A_50)) | ~r2_hidden(C_107, k2_relat_1(k1_wellord2(A_50))))), inference(superposition, [status(thm), theory('equality')], [c_70, c_277])).
% 6.13/2.13  tff(c_321, plain, (![C_109, A_110]: (r2_hidden(C_109, A_110) | ~r2_hidden(C_109, k2_relat_1(k1_wellord2(A_110))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_310])).
% 6.13/2.13  tff(c_370, plain, (![A_116, B_117]: (r2_hidden('#skF_1'(k2_relat_1(k1_wellord2(A_116)), B_117), A_116) | r1_tarski(k2_relat_1(k1_wellord2(A_116)), B_117))), inference(resolution, [status(thm)], [c_6, c_321])).
% 6.13/2.13  tff(c_389, plain, (![A_118]: (r1_tarski(k2_relat_1(k1_wellord2(A_118)), A_118))), inference(resolution, [status(thm)], [c_370, c_4])).
% 6.13/2.13  tff(c_392, plain, (![A_118]: (k2_relat_1(k1_wellord2(A_118))=A_118 | ~r1_tarski(A_118, k2_relat_1(k1_wellord2(A_118))))), inference(resolution, [status(thm)], [c_389, c_8])).
% 6.13/2.13  tff(c_4534, plain, (![A_309]: (k2_relat_1(k1_wellord2(A_309))=A_309)), inference(demodulation, [status(thm), theory('equality')], [c_4461, c_392])).
% 6.13/2.13  tff(c_38, plain, (![A_46]: (r1_tarski(A_46, k2_zfmisc_1(k1_relat_1(A_46), k2_relat_1(A_46))) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.13/2.13  tff(c_4570, plain, (![A_309]: (r1_tarski(k1_wellord2(A_309), k2_zfmisc_1(k1_relat_1(k1_wellord2(A_309)), A_309)) | ~v1_relat_1(k1_wellord2(A_309)))), inference(superposition, [status(thm), theory('equality')], [c_4534, c_38])).
% 6.13/2.13  tff(c_4592, plain, (![A_309]: (r1_tarski(k1_wellord2(A_309), k2_zfmisc_1(A_309, A_309)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3637, c_4570])).
% 6.13/2.13  tff(c_64, plain, (~r1_tarski(k1_wellord2('#skF_12'), k2_zfmisc_1('#skF_12', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.13/2.13  tff(c_4618, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4592, c_64])).
% 6.13/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.13/2.13  
% 6.13/2.13  Inference rules
% 6.13/2.13  ----------------------
% 6.13/2.13  #Ref     : 0
% 6.13/2.13  #Sup     : 987
% 6.13/2.13  #Fact    : 0
% 6.13/2.13  #Define  : 0
% 6.13/2.13  #Split   : 0
% 6.13/2.13  #Chain   : 0
% 6.13/2.13  #Close   : 0
% 6.13/2.13  
% 6.13/2.13  Ordering : KBO
% 6.13/2.13  
% 6.13/2.13  Simplification rules
% 6.13/2.13  ----------------------
% 6.13/2.13  #Subsume      : 78
% 6.13/2.13  #Demod        : 331
% 6.13/2.13  #Tautology    : 122
% 6.13/2.13  #SimpNegUnit  : 0
% 6.13/2.13  #BackRed      : 60
% 6.13/2.13  
% 6.13/2.13  #Partial instantiations: 0
% 6.13/2.13  #Strategies tried      : 1
% 6.13/2.13  
% 6.13/2.13  Timing (in seconds)
% 6.13/2.13  ----------------------
% 6.13/2.14  Preprocessing        : 0.30
% 6.13/2.14  Parsing              : 0.15
% 6.13/2.14  CNF conversion       : 0.03
% 6.13/2.14  Main loop            : 1.07
% 6.13/2.14  Inferencing          : 0.33
% 6.13/2.14  Reduction            : 0.30
% 6.13/2.14  Demodulation         : 0.21
% 6.13/2.14  BG Simplification    : 0.05
% 6.13/2.14  Subsumption          : 0.31
% 6.13/2.14  Abstraction          : 0.06
% 6.13/2.14  MUC search           : 0.00
% 6.13/2.14  Cooper               : 0.00
% 6.13/2.14  Total                : 1.41
% 6.13/2.14  Index Insertion      : 0.00
% 6.13/2.14  Index Deletion       : 0.00
% 6.13/2.14  Index Matching       : 0.00
% 6.13/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

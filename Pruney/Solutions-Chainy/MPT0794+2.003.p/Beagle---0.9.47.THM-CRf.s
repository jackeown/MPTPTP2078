%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:48 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 188 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 824 expanded)
%              Number of equality atoms :   19 ( 150 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k3_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( r3_wellord1(A,B,C)
                 => ! [D,E] :
                      ( r2_hidden(k4_tarski(D,E),A)
                     => ( D = E
                        | ( r2_hidden(k4_tarski(k1_funct_1(C,D),k1_funct_1(C,E)),B)
                          & k1_funct_1(C,D) != k1_funct_1(C,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
              <=> ( k1_relat_1(C) = k3_relat_1(A)
                  & k2_relat_1(C) = k3_relat_1(B)
                  & v2_funct_1(C)
                  & ! [D,E] :
                      ( r2_hidden(k4_tarski(D,E),A)
                    <=> ( r2_hidden(D,k3_relat_1(A))
                        & r2_hidden(E,k3_relat_1(A))
                        & r2_hidden(k4_tarski(k1_funct_1(C,D),k1_funct_1(C,E)),B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( v2_funct_1(B)
          & r2_hidden(A,k1_relat_1(B)) )
       => ( A = k1_funct_1(k2_funct_1(B),k1_funct_1(B,A))
          & A = k1_funct_1(k5_relat_1(B,k2_funct_1(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_42,plain,(
    r3_wellord1('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    '#skF_9' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_51,plain,(
    ! [C_58,A_59,B_60] :
      ( v2_funct_1(C_58)
      | ~ r3_wellord1(A_59,B_60,C_58)
      | ~ v1_funct_1(C_58)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_54,plain,
    ( v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_51])).

tff(c_57,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_54])).

tff(c_40,plain,(
    r2_hidden(k4_tarski('#skF_8','#skF_9'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_140,plain,(
    ! [C_85,D_88,E_87,B_89,A_86] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_85,D_88),k1_funct_1(C_85,E_87)),B_89)
      | ~ r2_hidden(k4_tarski(D_88,E_87),A_86)
      | ~ r3_wellord1(A_86,B_89,C_85)
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_142,plain,(
    ! [C_85,B_89] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_85,'#skF_8'),k1_funct_1(C_85,'#skF_9')),B_89)
      | ~ r3_wellord1('#skF_5',B_89,C_85)
      | ~ v1_funct_1(C_85)
      | ~ v1_relat_1(C_85)
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_140])).

tff(c_146,plain,(
    ! [C_90,B_91] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_90,'#skF_8'),k1_funct_1(C_90,'#skF_9')),B_91)
      | ~ r3_wellord1('#skF_5',B_91,C_90)
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90)
      | ~ v1_relat_1(B_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_142])).

tff(c_36,plain,
    ( k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_7','#skF_8')
    | ~ r2_hidden(k4_tarski(k1_funct_1('#skF_7','#skF_8'),k1_funct_1('#skF_7','#skF_9')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    ~ r2_hidden(k4_tarski(k1_funct_1('#skF_7','#skF_8'),k1_funct_1('#skF_7','#skF_9')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_155,plain,
    ( ~ r3_wellord1('#skF_5','#skF_6','#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_146,c_58])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_155])).

tff(c_171,plain,(
    k1_funct_1('#skF_7','#skF_9') = k1_funct_1('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_200,plain,(
    ! [B_98,A_99] :
      ( k1_funct_1(k2_funct_1(B_98),k1_funct_1(B_98,A_99)) = A_99
      | ~ r2_hidden(A_99,k1_relat_1(B_98))
      | ~ v2_funct_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_215,plain,
    ( k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) = '#skF_9'
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_200])).

tff(c_219,plain,
    ( k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) = '#skF_9'
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_57,c_215])).

tff(c_220,plain,(
    ~ r2_hidden('#skF_9',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_189,plain,(
    ! [A_95,C_96,B_97] :
      ( k3_relat_1(A_95) = k1_relat_1(C_96)
      | ~ r3_wellord1(A_95,B_97,C_96)
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96)
      | ~ v1_relat_1(B_97)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_192,plain,
    ( k3_relat_1('#skF_5') = k1_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_189])).

tff(c_195,plain,(
    k3_relat_1('#skF_5') = k1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_192])).

tff(c_233,plain,(
    ! [E_104,C_102,A_103,D_105,B_106] :
      ( r2_hidden(E_104,k3_relat_1(A_103))
      | ~ r2_hidden(k4_tarski(D_105,E_104),A_103)
      | ~ r3_wellord1(A_103,B_106,C_102)
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_237,plain,(
    ! [B_106,C_102] :
      ( r2_hidden('#skF_9',k3_relat_1('#skF_5'))
      | ~ r3_wellord1('#skF_5',B_106,C_102)
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_233])).

tff(c_243,plain,(
    ! [B_106,C_102] :
      ( r2_hidden('#skF_9',k1_relat_1('#skF_7'))
      | ~ r3_wellord1('#skF_5',B_106,C_102)
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_195,c_237])).

tff(c_245,plain,(
    ! [B_107,C_108] :
      ( ~ r3_wellord1('#skF_5',B_107,C_108)
      | ~ v1_funct_1(C_108)
      | ~ v1_relat_1(C_108)
      | ~ v1_relat_1(B_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_243])).

tff(c_248,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_245])).

tff(c_252,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_248])).

tff(c_253,plain,(
    k1_funct_1(k2_funct_1('#skF_7'),k1_funct_1('#skF_7','#skF_8')) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( k1_funct_1(k2_funct_1(B_2),k1_funct_1(B_2,A_1)) = A_1
      | ~ r2_hidden(A_1,k1_relat_1(B_2))
      | ~ v2_funct_1(B_2)
      | ~ v1_funct_1(B_2)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_261,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_4])).

tff(c_268,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_57,c_261])).

tff(c_269,plain,(
    ~ r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_268])).

tff(c_297,plain,(
    ! [A_117,D_119,B_120,C_116,E_118] :
      ( r2_hidden(D_119,k3_relat_1(A_117))
      | ~ r2_hidden(k4_tarski(D_119,E_118),A_117)
      | ~ r3_wellord1(A_117,B_120,C_116)
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_301,plain,(
    ! [B_120,C_116] :
      ( r2_hidden('#skF_8',k3_relat_1('#skF_5'))
      | ~ r3_wellord1('#skF_5',B_120,C_116)
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | ~ v1_relat_1(B_120)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_297])).

tff(c_307,plain,(
    ! [B_120,C_116] :
      ( r2_hidden('#skF_8',k1_relat_1('#skF_7'))
      | ~ r3_wellord1('#skF_5',B_120,C_116)
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116)
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_195,c_301])).

tff(c_309,plain,(
    ! [B_121,C_122] :
      ( ~ r3_wellord1('#skF_5',B_121,C_122)
      | ~ v1_funct_1(C_122)
      | ~ v1_relat_1(C_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_307])).

tff(c_312,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_309])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:52:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  
% 2.51/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.37  %$ r3_wellord1 > r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k3_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 2.51/1.37  
% 2.51/1.37  %Foreground sorts:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Background operators:
% 2.51/1.37  
% 2.51/1.37  
% 2.51/1.37  %Foreground operators:
% 2.51/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.51/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.51/1.37  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 2.51/1.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.51/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.51/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.51/1.37  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.51/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.51/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.51/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.51/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.51/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.51/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.51/1.37  tff('#skF_9', type, '#skF_9': $i).
% 2.51/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.51/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.51/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.51/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.51/1.37  
% 2.51/1.39  tff(f_87, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) => (![D, E]: (r2_hidden(k4_tarski(D, E), A) => ((D = E) | (r2_hidden(k4_tarski(k1_funct_1(C, D), k1_funct_1(C, E)), B) & ~(k1_funct_1(C, D) = k1_funct_1(C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_wellord1)).
% 2.51/1.39  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) <=> ((((k1_relat_1(C) = k3_relat_1(A)) & (k2_relat_1(C) = k3_relat_1(B))) & v2_funct_1(C)) & (![D, E]: (r2_hidden(k4_tarski(D, E), A) <=> ((r2_hidden(D, k3_relat_1(A)) & r2_hidden(E, k3_relat_1(A))) & r2_hidden(k4_tarski(k1_funct_1(C, D), k1_funct_1(C, E)), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_wellord1)).
% 2.51/1.39  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(B) & r2_hidden(A, k1_relat_1(B))) => ((A = k1_funct_1(k2_funct_1(B), k1_funct_1(B, A))) & (A = k1_funct_1(k5_relat_1(B, k2_funct_1(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_funct_1)).
% 2.51/1.39  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_46, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_42, plain, (r3_wellord1('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_38, plain, ('#skF_9'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_51, plain, (![C_58, A_59, B_60]: (v2_funct_1(C_58) | ~r3_wellord1(A_59, B_60, C_58) | ~v1_funct_1(C_58) | ~v1_relat_1(C_58) | ~v1_relat_1(B_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.39  tff(c_54, plain, (v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_51])).
% 2.51/1.39  tff(c_57, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_54])).
% 2.51/1.39  tff(c_40, plain, (r2_hidden(k4_tarski('#skF_8', '#skF_9'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_140, plain, (![C_85, D_88, E_87, B_89, A_86]: (r2_hidden(k4_tarski(k1_funct_1(C_85, D_88), k1_funct_1(C_85, E_87)), B_89) | ~r2_hidden(k4_tarski(D_88, E_87), A_86) | ~r3_wellord1(A_86, B_89, C_85) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85) | ~v1_relat_1(B_89) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.39  tff(c_142, plain, (![C_85, B_89]: (r2_hidden(k4_tarski(k1_funct_1(C_85, '#skF_8'), k1_funct_1(C_85, '#skF_9')), B_89) | ~r3_wellord1('#skF_5', B_89, C_85) | ~v1_funct_1(C_85) | ~v1_relat_1(C_85) | ~v1_relat_1(B_89) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_140])).
% 2.51/1.39  tff(c_146, plain, (![C_90, B_91]: (r2_hidden(k4_tarski(k1_funct_1(C_90, '#skF_8'), k1_funct_1(C_90, '#skF_9')), B_91) | ~r3_wellord1('#skF_5', B_91, C_90) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90) | ~v1_relat_1(B_91))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_142])).
% 2.51/1.39  tff(c_36, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_7', '#skF_8') | ~r2_hidden(k4_tarski(k1_funct_1('#skF_7', '#skF_8'), k1_funct_1('#skF_7', '#skF_9')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.51/1.39  tff(c_58, plain, (~r2_hidden(k4_tarski(k1_funct_1('#skF_7', '#skF_8'), k1_funct_1('#skF_7', '#skF_9')), '#skF_6')), inference(splitLeft, [status(thm)], [c_36])).
% 2.51/1.39  tff(c_155, plain, (~r3_wellord1('#skF_5', '#skF_6', '#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_146, c_58])).
% 2.51/1.39  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_155])).
% 2.51/1.39  tff(c_171, plain, (k1_funct_1('#skF_7', '#skF_9')=k1_funct_1('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_36])).
% 2.51/1.39  tff(c_200, plain, (![B_98, A_99]: (k1_funct_1(k2_funct_1(B_98), k1_funct_1(B_98, A_99))=A_99 | ~r2_hidden(A_99, k1_relat_1(B_98)) | ~v2_funct_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.39  tff(c_215, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))='#skF_9' | ~r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_171, c_200])).
% 2.51/1.39  tff(c_219, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))='#skF_9' | ~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_57, c_215])).
% 2.51/1.39  tff(c_220, plain, (~r2_hidden('#skF_9', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_219])).
% 2.51/1.39  tff(c_189, plain, (![A_95, C_96, B_97]: (k3_relat_1(A_95)=k1_relat_1(C_96) | ~r3_wellord1(A_95, B_97, C_96) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96) | ~v1_relat_1(B_97) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.39  tff(c_192, plain, (k3_relat_1('#skF_5')=k1_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_189])).
% 2.51/1.39  tff(c_195, plain, (k3_relat_1('#skF_5')=k1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_192])).
% 2.51/1.39  tff(c_233, plain, (![E_104, C_102, A_103, D_105, B_106]: (r2_hidden(E_104, k3_relat_1(A_103)) | ~r2_hidden(k4_tarski(D_105, E_104), A_103) | ~r3_wellord1(A_103, B_106, C_102) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102) | ~v1_relat_1(B_106) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.39  tff(c_237, plain, (![B_106, C_102]: (r2_hidden('#skF_9', k3_relat_1('#skF_5')) | ~r3_wellord1('#skF_5', B_106, C_102) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102) | ~v1_relat_1(B_106) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_233])).
% 2.51/1.39  tff(c_243, plain, (![B_106, C_102]: (r2_hidden('#skF_9', k1_relat_1('#skF_7')) | ~r3_wellord1('#skF_5', B_106, C_102) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102) | ~v1_relat_1(B_106))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_195, c_237])).
% 2.51/1.39  tff(c_245, plain, (![B_107, C_108]: (~r3_wellord1('#skF_5', B_107, C_108) | ~v1_funct_1(C_108) | ~v1_relat_1(C_108) | ~v1_relat_1(B_107))), inference(negUnitSimplification, [status(thm)], [c_220, c_243])).
% 2.51/1.39  tff(c_248, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_245])).
% 2.51/1.39  tff(c_252, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_248])).
% 2.51/1.39  tff(c_253, plain, (k1_funct_1(k2_funct_1('#skF_7'), k1_funct_1('#skF_7', '#skF_8'))='#skF_9'), inference(splitRight, [status(thm)], [c_219])).
% 2.51/1.39  tff(c_4, plain, (![B_2, A_1]: (k1_funct_1(k2_funct_1(B_2), k1_funct_1(B_2, A_1))=A_1 | ~r2_hidden(A_1, k1_relat_1(B_2)) | ~v2_funct_1(B_2) | ~v1_funct_1(B_2) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.51/1.39  tff(c_261, plain, ('#skF_9'='#skF_8' | ~r2_hidden('#skF_8', k1_relat_1('#skF_7')) | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_253, c_4])).
% 2.51/1.39  tff(c_268, plain, ('#skF_9'='#skF_8' | ~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_57, c_261])).
% 2.51/1.39  tff(c_269, plain, (~r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_38, c_268])).
% 2.51/1.39  tff(c_297, plain, (![A_117, D_119, B_120, C_116, E_118]: (r2_hidden(D_119, k3_relat_1(A_117)) | ~r2_hidden(k4_tarski(D_119, E_118), A_117) | ~r3_wellord1(A_117, B_120, C_116) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116) | ~v1_relat_1(B_120) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.51/1.39  tff(c_301, plain, (![B_120, C_116]: (r2_hidden('#skF_8', k3_relat_1('#skF_5')) | ~r3_wellord1('#skF_5', B_120, C_116) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116) | ~v1_relat_1(B_120) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_297])).
% 2.51/1.39  tff(c_307, plain, (![B_120, C_116]: (r2_hidden('#skF_8', k1_relat_1('#skF_7')) | ~r3_wellord1('#skF_5', B_120, C_116) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_195, c_301])).
% 2.51/1.39  tff(c_309, plain, (![B_121, C_122]: (~r3_wellord1('#skF_5', B_121, C_122) | ~v1_funct_1(C_122) | ~v1_relat_1(C_122) | ~v1_relat_1(B_121))), inference(negUnitSimplification, [status(thm)], [c_269, c_307])).
% 2.51/1.39  tff(c_312, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_42, c_309])).
% 2.51/1.39  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_312])).
% 2.51/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.39  
% 2.51/1.39  Inference rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Ref     : 0
% 2.51/1.39  #Sup     : 57
% 2.51/1.39  #Fact    : 0
% 2.51/1.39  #Define  : 0
% 2.51/1.39  #Split   : 4
% 2.51/1.39  #Chain   : 0
% 2.51/1.39  #Close   : 0
% 2.51/1.39  
% 2.51/1.39  Ordering : KBO
% 2.51/1.39  
% 2.51/1.39  Simplification rules
% 2.51/1.39  ----------------------
% 2.51/1.39  #Subsume      : 1
% 2.51/1.39  #Demod        : 64
% 2.51/1.39  #Tautology    : 23
% 2.51/1.39  #SimpNegUnit  : 4
% 2.51/1.39  #BackRed      : 0
% 2.51/1.39  
% 2.51/1.39  #Partial instantiations: 0
% 2.51/1.39  #Strategies tried      : 1
% 2.51/1.39  
% 2.51/1.39  Timing (in seconds)
% 2.51/1.39  ----------------------
% 2.51/1.39  Preprocessing        : 0.34
% 2.51/1.39  Parsing              : 0.17
% 2.51/1.39  CNF conversion       : 0.03
% 2.51/1.39  Main loop            : 0.22
% 2.51/1.39  Inferencing          : 0.08
% 2.51/1.39  Reduction            : 0.07
% 2.51/1.39  Demodulation         : 0.05
% 2.51/1.39  BG Simplification    : 0.02
% 2.51/1.39  Subsumption          : 0.04
% 2.51/1.39  Abstraction          : 0.01
% 2.51/1.39  MUC search           : 0.00
% 2.51/1.39  Cooper               : 0.00
% 2.51/1.39  Total                : 0.59
% 2.51/1.39  Index Insertion      : 0.00
% 2.51/1.39  Index Deletion       : 0.00
% 2.51/1.39  Index Matching       : 0.00
% 2.51/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

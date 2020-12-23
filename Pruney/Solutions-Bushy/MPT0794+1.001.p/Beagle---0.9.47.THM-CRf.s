%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0794+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:51 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 186 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :    8
%              Number of atoms          :  159 ( 843 expanded)
%              Number of equality atoms :   19 ( 149 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r2_hidden > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_5 > #skF_1 > #skF_11 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_89,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_wellord1)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_wellord1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(c_44,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    r3_wellord1('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_207,plain,(
    ! [A_111,C_112,B_113] :
      ( k3_relat_1(A_111) = k1_relat_1(C_112)
      | ~ r3_wellord1(A_111,B_113,C_112)
      | ~ v1_funct_1(C_112)
      | ~ v1_relat_1(C_112)
      | ~ v1_relat_1(B_113)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_210,plain,
    ( k3_relat_1('#skF_7') = k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_207])).

tff(c_213,plain,(
    k3_relat_1('#skF_7') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_210])).

tff(c_46,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_218,plain,(
    ! [D_115,A_118,B_116,C_117,E_114] :
      ( r2_hidden(D_115,k3_relat_1(A_118))
      | ~ r2_hidden(k4_tarski(D_115,E_114),A_118)
      | ~ r3_wellord1(A_118,B_116,C_117)
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117)
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_222,plain,(
    ! [B_116,C_117] :
      ( r2_hidden('#skF_10',k3_relat_1('#skF_7'))
      | ~ r3_wellord1('#skF_7',B_116,C_117)
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117)
      | ~ v1_relat_1(B_116)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_218])).

tff(c_228,plain,(
    ! [B_116,C_117] :
      ( r2_hidden('#skF_10',k1_relat_1('#skF_9'))
      | ~ r3_wellord1('#skF_7',B_116,C_117)
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117)
      | ~ v1_relat_1(B_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_213,c_222])).

tff(c_230,plain,(
    ! [B_119,C_120] :
      ( ~ r3_wellord1('#skF_7',B_119,C_120)
      | ~ v1_funct_1(C_120)
      | ~ v1_relat_1(C_120)
      | ~ v1_relat_1(B_119) ) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_233,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_233])).

tff(c_238,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_189,plain,(
    ! [C_105,A_106,B_107] :
      ( v2_funct_1(C_105)
      | ~ r3_wellord1(A_106,B_107,C_105)
      | ~ v1_funct_1(C_105)
      | ~ v1_relat_1(C_105)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_192,plain,
    ( v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_189])).

tff(c_195,plain,(
    v2_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_192])).

tff(c_239,plain,(
    ! [E_121,D_122,A_125,B_123,C_124] :
      ( r2_hidden(E_121,k3_relat_1(A_125))
      | ~ r2_hidden(k4_tarski(D_122,E_121),A_125)
      | ~ r3_wellord1(A_125,B_123,C_124)
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_243,plain,(
    ! [B_123,C_124] :
      ( r2_hidden('#skF_11',k3_relat_1('#skF_7'))
      | ~ r3_wellord1('#skF_7',B_123,C_124)
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_239])).

tff(c_249,plain,(
    ! [B_123,C_124] :
      ( r2_hidden('#skF_11',k1_relat_1('#skF_9'))
      | ~ r3_wellord1('#skF_7',B_123,C_124)
      | ~ v1_funct_1(C_124)
      | ~ v1_relat_1(C_124)
      | ~ v1_relat_1(B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_213,c_243])).

tff(c_251,plain,(
    ! [B_126,C_127] :
      ( ~ r3_wellord1('#skF_7',B_126,C_127)
      | ~ v1_funct_1(C_127)
      | ~ v1_relat_1(C_127)
      | ~ v1_relat_1(B_126) ) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_254,plain,
    ( ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_251])).

tff(c_258,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_254])).

tff(c_259,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_149,plain,(
    ! [C_99,B_98,E_96,D_97,A_100] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_99,D_97),k1_funct_1(C_99,E_96)),B_98)
      | ~ r2_hidden(k4_tarski(D_97,E_96),A_100)
      | ~ r3_wellord1(A_100,B_98,C_99)
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_151,plain,(
    ! [C_99,B_98] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_99,'#skF_10'),k1_funct_1(C_99,'#skF_11')),B_98)
      | ~ r3_wellord1('#skF_7',B_98,C_99)
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_46,c_149])).

tff(c_155,plain,(
    ! [C_101,B_102] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_101,'#skF_10'),k1_funct_1(C_101,'#skF_11')),B_102)
      | ~ r3_wellord1('#skF_7',B_102,C_101)
      | ~ v1_funct_1(C_101)
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_151])).

tff(c_42,plain,
    ( k1_funct_1('#skF_9','#skF_11') = k1_funct_1('#skF_9','#skF_10')
    | ~ r2_hidden(k4_tarski(k1_funct_1('#skF_9','#skF_10'),k1_funct_1('#skF_9','#skF_11')),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_59,plain,(
    ~ r2_hidden(k4_tarski(k1_funct_1('#skF_9','#skF_10'),k1_funct_1('#skF_9','#skF_11')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_164,plain,
    ( ~ r3_wellord1('#skF_7','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_155,c_59])).

tff(c_171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_164])).

tff(c_172,plain,(
    k1_funct_1('#skF_9','#skF_11') = k1_funct_1('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_266,plain,(
    ! [C_130,B_131,A_132] :
      ( C_130 = B_131
      | k1_funct_1(A_132,C_130) != k1_funct_1(A_132,B_131)
      | ~ r2_hidden(C_130,k1_relat_1(A_132))
      | ~ r2_hidden(B_131,k1_relat_1(A_132))
      | ~ v2_funct_1(A_132)
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_272,plain,(
    ! [B_131] :
      ( B_131 = '#skF_11'
      | k1_funct_1('#skF_9',B_131) != k1_funct_1('#skF_9','#skF_10')
      | ~ r2_hidden('#skF_11',k1_relat_1('#skF_9'))
      | ~ r2_hidden(B_131,k1_relat_1('#skF_9'))
      | ~ v2_funct_1('#skF_9')
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_266])).

tff(c_279,plain,(
    ! [B_133] :
      ( B_133 = '#skF_11'
      | k1_funct_1('#skF_9',B_133) != k1_funct_1('#skF_9','#skF_10')
      | ~ r2_hidden(B_133,k1_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_195,c_259,c_272])).

tff(c_285,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_238,c_279])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_285])).

%------------------------------------------------------------------------------

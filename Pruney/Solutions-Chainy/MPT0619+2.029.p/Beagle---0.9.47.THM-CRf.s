%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:55 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 250 expanded)
%              Number of leaves         :   35 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  139 ( 546 expanded)
%              Number of equality atoms :   67 ( 283 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_83,plain,(
    ! [A_43] :
      ( k2_relat_1(A_43) != k1_xboole_0
      | k1_xboole_0 = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_87,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_83])).

tff(c_88,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_18,plain,(
    ! [A_23,B_24] :
      ( r2_hidden('#skF_1'(A_23,B_24),A_23)
      | k1_xboole_0 = A_23
      | k1_tarski(B_24) = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    k1_tarski('#skF_2') = k1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_135,plain,(
    ! [A_61,B_62] :
      ( k9_relat_1(A_61,k1_tarski(B_62)) = k11_relat_1(A_61,B_62)
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_148,plain,(
    ! [A_65] :
      ( k9_relat_1(A_65,k1_relat_1('#skF_3')) = k11_relat_1(A_65,'#skF_2')
      | ~ v1_relat_1(A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_135])).

tff(c_28,plain,(
    ! [A_32] :
      ( k9_relat_1(A_32,k1_relat_1(A_32)) = k2_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_155,plain,
    ( k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_28])).

tff(c_165,plain,(
    k11_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_155])).

tff(c_30,plain,(
    ! [A_33,B_34,C_35] :
      ( r2_hidden(k4_tarski(A_33,B_34),C_35)
      | ~ r2_hidden(B_34,k11_relat_1(C_35,A_33))
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_223,plain,(
    ! [C_87,A_88,B_89] :
      ( k1_funct_1(C_87,A_88) = B_89
      | ~ r2_hidden(k4_tarski(A_88,B_89),C_87)
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_233,plain,(
    ! [C_93,A_94,B_95] :
      ( k1_funct_1(C_93,A_94) = B_95
      | ~ v1_funct_1(C_93)
      | ~ r2_hidden(B_95,k11_relat_1(C_93,A_94))
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_30,c_223])).

tff(c_240,plain,(
    ! [B_95] :
      ( k1_funct_1('#skF_3','#skF_2') = B_95
      | ~ v1_funct_1('#skF_3')
      | ~ r2_hidden(B_95,k2_relat_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_233])).

tff(c_249,plain,(
    ! [B_96] :
      ( k1_funct_1('#skF_3','#skF_2') = B_96
      | ~ r2_hidden(B_96,k2_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_240])).

tff(c_257,plain,(
    ! [B_24] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_24) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_24) ) ),
    inference(resolution,[status(thm)],[c_18,c_249])).

tff(c_262,plain,(
    ! [B_97] :
      ( '#skF_1'(k2_relat_1('#skF_3'),B_97) = k1_funct_1('#skF_3','#skF_2')
      | k2_relat_1('#skF_3') = k1_tarski(B_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_257])).

tff(c_16,plain,(
    ! [A_23,B_24] :
      ( '#skF_1'(A_23,B_24) != B_24
      | k1_xboole_0 = A_23
      | k1_tarski(B_24) = A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_270,plain,(
    ! [B_97] :
      ( k1_funct_1('#skF_3','#skF_2') != B_97
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k2_relat_1('#skF_3') = k1_tarski(B_97)
      | k2_relat_1('#skF_3') = k1_tarski(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_16])).

tff(c_278,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) = k2_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_270])).

tff(c_48,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != k2_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_48])).

tff(c_282,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_289,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_282,c_36])).

tff(c_77,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) != k1_xboole_0
      | k1_xboole_0 = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_81,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_82,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_285,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_82])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_285])).

tff(c_322,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_323,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_332,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_323])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_325,plain,(
    ! [A_1] : r1_tarski('#skF_3',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_2])).

tff(c_333,plain,(
    k1_tarski('#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_50])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_375,plain,(
    ! [A_106,C_107,B_108] :
      ( r2_hidden(A_106,C_107)
      | ~ r1_tarski(k2_tarski(A_106,B_108),C_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_379,plain,(
    ! [A_109,C_110] :
      ( r2_hidden(A_109,C_110)
      | ~ r1_tarski(k1_tarski(A_109),C_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_375])).

tff(c_382,plain,(
    ! [C_110] :
      ( r2_hidden('#skF_2',C_110)
      | ~ r1_tarski('#skF_3',C_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_379])).

tff(c_384,plain,(
    ! [C_110] : r2_hidden('#skF_2',C_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_325,c_382])).

tff(c_480,plain,(
    ! [A_141,C_142,B_143] :
      ( r2_hidden(A_141,k1_relat_1(C_142))
      | ~ r2_hidden(k4_tarski(A_141,B_143),C_142)
      | ~ v1_funct_1(C_142)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_499,plain,(
    ! [A_152,C_153,B_154] :
      ( r2_hidden(A_152,k1_relat_1(C_153))
      | ~ v1_funct_1(C_153)
      | ~ r2_hidden(B_154,k11_relat_1(C_153,A_152))
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_30,c_480])).

tff(c_515,plain,(
    ! [A_155,C_156] :
      ( r2_hidden(A_155,k1_relat_1(C_156))
      | ~ v1_funct_1(C_156)
      | ~ v1_relat_1(C_156) ) ),
    inference(resolution,[status(thm)],[c_384,c_499])).

tff(c_526,plain,(
    ! [A_155] :
      ( r2_hidden(A_155,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_515])).

tff(c_531,plain,(
    ! [A_157] : r2_hidden(A_157,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_526])).

tff(c_44,plain,(
    ! [C_39,A_37,B_38] :
      ( k1_funct_1(C_39,A_37) = B_38
      | ~ r2_hidden(k4_tarski(A_37,B_38),C_39)
      | ~ v1_funct_1(C_39)
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_535,plain,(
    ! [A_37,B_38] :
      ( k1_funct_1('#skF_3',A_37) = B_38
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_531,c_44])).

tff(c_549,plain,(
    ! [A_158] : k1_funct_1('#skF_3',A_158) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_535])).

tff(c_542,plain,(
    ! [A_37,B_38] : k1_funct_1('#skF_3',A_37) = B_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_535])).

tff(c_763,plain,(
    ! [B_1661] : B_1661 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_542])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_326,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_322,c_34])).

tff(c_339,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_48])).

tff(c_823,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_763,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.35  % CPULimit   : 60
% 0.19/0.35  % DateTime   : Tue Dec  1 12:58:08 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  
% 2.70/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.42  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.42  
% 2.70/1.42  %Foreground sorts:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Background operators:
% 2.70/1.42  
% 2.70/1.42  
% 2.70/1.42  %Foreground operators:
% 2.70/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.70/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.70/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.70/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.70/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.42  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.70/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.42  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.70/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.70/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.42  
% 2.70/1.43  tff(f_104, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 2.70/1.43  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.70/1.43  tff(f_53, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 2.70/1.43  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.70/1.43  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.70/1.43  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.70/1.43  tff(f_95, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.70/1.43  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.70/1.43  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.70/1.43  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.70/1.43  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.70/1.43  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.43  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.43  tff(c_83, plain, (![A_43]: (k2_relat_1(A_43)!=k1_xboole_0 | k1_xboole_0=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.70/1.43  tff(c_87, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_83])).
% 2.70/1.43  tff(c_88, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_87])).
% 2.70/1.43  tff(c_18, plain, (![A_23, B_24]: (r2_hidden('#skF_1'(A_23, B_24), A_23) | k1_xboole_0=A_23 | k1_tarski(B_24)=A_23)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.43  tff(c_50, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.43  tff(c_135, plain, (![A_61, B_62]: (k9_relat_1(A_61, k1_tarski(B_62))=k11_relat_1(A_61, B_62) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.70/1.43  tff(c_148, plain, (![A_65]: (k9_relat_1(A_65, k1_relat_1('#skF_3'))=k11_relat_1(A_65, '#skF_2') | ~v1_relat_1(A_65))), inference(superposition, [status(thm), theory('equality')], [c_50, c_135])).
% 2.70/1.43  tff(c_28, plain, (![A_32]: (k9_relat_1(A_32, k1_relat_1(A_32))=k2_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.70/1.43  tff(c_155, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_148, c_28])).
% 2.70/1.43  tff(c_165, plain, (k11_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_155])).
% 2.70/1.43  tff(c_30, plain, (![A_33, B_34, C_35]: (r2_hidden(k4_tarski(A_33, B_34), C_35) | ~r2_hidden(B_34, k11_relat_1(C_35, A_33)) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.70/1.43  tff(c_223, plain, (![C_87, A_88, B_89]: (k1_funct_1(C_87, A_88)=B_89 | ~r2_hidden(k4_tarski(A_88, B_89), C_87) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.43  tff(c_233, plain, (![C_93, A_94, B_95]: (k1_funct_1(C_93, A_94)=B_95 | ~v1_funct_1(C_93) | ~r2_hidden(B_95, k11_relat_1(C_93, A_94)) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_30, c_223])).
% 2.70/1.43  tff(c_240, plain, (![B_95]: (k1_funct_1('#skF_3', '#skF_2')=B_95 | ~v1_funct_1('#skF_3') | ~r2_hidden(B_95, k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_233])).
% 2.70/1.43  tff(c_249, plain, (![B_96]: (k1_funct_1('#skF_3', '#skF_2')=B_96 | ~r2_hidden(B_96, k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_240])).
% 2.70/1.43  tff(c_257, plain, (![B_24]: ('#skF_1'(k2_relat_1('#skF_3'), B_24)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_24))), inference(resolution, [status(thm)], [c_18, c_249])).
% 2.70/1.43  tff(c_262, plain, (![B_97]: ('#skF_1'(k2_relat_1('#skF_3'), B_97)=k1_funct_1('#skF_3', '#skF_2') | k2_relat_1('#skF_3')=k1_tarski(B_97))), inference(negUnitSimplification, [status(thm)], [c_88, c_257])).
% 2.70/1.43  tff(c_16, plain, (![A_23, B_24]: ('#skF_1'(A_23, B_24)!=B_24 | k1_xboole_0=A_23 | k1_tarski(B_24)=A_23)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.70/1.43  tff(c_270, plain, (![B_97]: (k1_funct_1('#skF_3', '#skF_2')!=B_97 | k2_relat_1('#skF_3')=k1_xboole_0 | k2_relat_1('#skF_3')=k1_tarski(B_97) | k2_relat_1('#skF_3')=k1_tarski(B_97))), inference(superposition, [status(thm), theory('equality')], [c_262, c_16])).
% 2.70/1.43  tff(c_278, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_88, c_270])).
% 2.70/1.43  tff(c_48, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!=k2_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.70/1.43  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_48])).
% 2.70/1.43  tff(c_282, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_87])).
% 2.70/1.43  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_289, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_282, c_36])).
% 2.70/1.43  tff(c_77, plain, (![A_42]: (k1_relat_1(A_42)!=k1_xboole_0 | k1_xboole_0=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.70/1.43  tff(c_81, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_54, c_77])).
% 2.70/1.43  tff(c_82, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_81])).
% 2.70/1.43  tff(c_285, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_82])).
% 2.70/1.43  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_285])).
% 2.70/1.43  tff(c_322, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_81])).
% 2.70/1.43  tff(c_323, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_81])).
% 2.70/1.43  tff(c_332, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_323])).
% 2.70/1.43  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.43  tff(c_325, plain, (![A_1]: (r1_tarski('#skF_3', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_2])).
% 2.70/1.43  tff(c_333, plain, (k1_tarski('#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_332, c_50])).
% 2.70/1.43  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.70/1.43  tff(c_375, plain, (![A_106, C_107, B_108]: (r2_hidden(A_106, C_107) | ~r1_tarski(k2_tarski(A_106, B_108), C_107))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.70/1.43  tff(c_379, plain, (![A_109, C_110]: (r2_hidden(A_109, C_110) | ~r1_tarski(k1_tarski(A_109), C_110))), inference(superposition, [status(thm), theory('equality')], [c_4, c_375])).
% 2.70/1.43  tff(c_382, plain, (![C_110]: (r2_hidden('#skF_2', C_110) | ~r1_tarski('#skF_3', C_110))), inference(superposition, [status(thm), theory('equality')], [c_333, c_379])).
% 2.70/1.43  tff(c_384, plain, (![C_110]: (r2_hidden('#skF_2', C_110))), inference(demodulation, [status(thm), theory('equality')], [c_325, c_382])).
% 2.70/1.43  tff(c_480, plain, (![A_141, C_142, B_143]: (r2_hidden(A_141, k1_relat_1(C_142)) | ~r2_hidden(k4_tarski(A_141, B_143), C_142) | ~v1_funct_1(C_142) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.43  tff(c_499, plain, (![A_152, C_153, B_154]: (r2_hidden(A_152, k1_relat_1(C_153)) | ~v1_funct_1(C_153) | ~r2_hidden(B_154, k11_relat_1(C_153, A_152)) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_30, c_480])).
% 2.70/1.43  tff(c_515, plain, (![A_155, C_156]: (r2_hidden(A_155, k1_relat_1(C_156)) | ~v1_funct_1(C_156) | ~v1_relat_1(C_156))), inference(resolution, [status(thm)], [c_384, c_499])).
% 2.70/1.43  tff(c_526, plain, (![A_155]: (r2_hidden(A_155, '#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_332, c_515])).
% 2.70/1.43  tff(c_531, plain, (![A_157]: (r2_hidden(A_157, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_526])).
% 2.70/1.43  tff(c_44, plain, (![C_39, A_37, B_38]: (k1_funct_1(C_39, A_37)=B_38 | ~r2_hidden(k4_tarski(A_37, B_38), C_39) | ~v1_funct_1(C_39) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.70/1.43  tff(c_535, plain, (![A_37, B_38]: (k1_funct_1('#skF_3', A_37)=B_38 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_531, c_44])).
% 2.70/1.43  tff(c_549, plain, (![A_158]: (k1_funct_1('#skF_3', A_158)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_535])).
% 2.70/1.43  tff(c_542, plain, (![A_37, B_38]: (k1_funct_1('#skF_3', A_37)=B_38)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_535])).
% 2.70/1.43  tff(c_763, plain, (![B_1661]: (B_1661='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_549, c_542])).
% 2.70/1.43  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.70/1.43  tff(c_326, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_322, c_34])).
% 2.70/1.43  tff(c_339, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_48])).
% 2.70/1.43  tff(c_823, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_763, c_339])).
% 2.70/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  Inference rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Ref     : 0
% 2.70/1.43  #Sup     : 198
% 2.70/1.43  #Fact    : 0
% 2.70/1.43  #Define  : 0
% 2.70/1.43  #Split   : 3
% 2.70/1.43  #Chain   : 0
% 2.70/1.43  #Close   : 0
% 2.70/1.43  
% 2.70/1.43  Ordering : KBO
% 2.70/1.43  
% 2.70/1.43  Simplification rules
% 2.70/1.43  ----------------------
% 2.70/1.43  #Subsume      : 32
% 2.70/1.43  #Demod        : 63
% 2.70/1.43  #Tautology    : 81
% 2.70/1.43  #SimpNegUnit  : 3
% 2.70/1.43  #BackRed      : 15
% 2.70/1.43  
% 2.70/1.43  #Partial instantiations: 629
% 2.70/1.43  #Strategies tried      : 1
% 2.70/1.43  
% 2.70/1.43  Timing (in seconds)
% 2.70/1.43  ----------------------
% 2.70/1.44  Preprocessing        : 0.32
% 2.70/1.44  Parsing              : 0.17
% 2.70/1.44  CNF conversion       : 0.02
% 2.70/1.44  Main loop            : 0.33
% 2.70/1.44  Inferencing          : 0.15
% 2.70/1.44  Reduction            : 0.08
% 2.70/1.44  Demodulation         : 0.06
% 2.70/1.44  BG Simplification    : 0.02
% 2.70/1.44  Subsumption          : 0.05
% 2.70/1.44  Abstraction          : 0.02
% 2.70/1.44  MUC search           : 0.00
% 2.70/1.44  Cooper               : 0.00
% 2.70/1.44  Total                : 0.69
% 2.70/1.44  Index Insertion      : 0.00
% 2.70/1.44  Index Deletion       : 0.00
% 2.70/1.44  Index Matching       : 0.00
% 2.70/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

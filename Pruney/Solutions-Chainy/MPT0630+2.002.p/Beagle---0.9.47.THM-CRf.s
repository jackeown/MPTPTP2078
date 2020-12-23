%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:18 EST 2020

% Result     : Theorem 9.81s
% Output     : CNFRefutation 9.81s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 156 expanded)
%              Number of leaves         :   36 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  169 ( 422 expanded)
%              Number of equality atoms :   12 (  56 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_17 > #skF_6 > #skF_3 > #skF_13 > #skF_16 > #skF_14 > #skF_12 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_15 > #skF_2 > #skF_8 > #skF_1 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
             => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_64,plain,(
    ~ r1_tarski(k2_relat_1('#skF_17'),k1_relat_1('#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_172,B_173] :
      ( r2_hidden('#skF_1'(A_172,B_173),A_172)
      | r1_tarski(A_172,B_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_172] : r1_tarski(A_172,A_172) ),
    inference(resolution,[status(thm)],[c_80,c_4])).

tff(c_66,plain,(
    k1_relat_1(k5_relat_1('#skF_17','#skF_16')) = k1_relat_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_70,plain,(
    v1_relat_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_68,plain,(
    v1_funct_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44,plain,(
    ! [A_126,C_162] :
      ( r2_hidden('#skF_15'(A_126,k2_relat_1(A_126),C_162),k1_relat_1(A_126))
      | ~ r2_hidden(C_162,k2_relat_1(A_126))
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_103,plain,(
    ! [C_188,A_189] :
      ( r2_hidden(k4_tarski(C_188,'#skF_5'(A_189,k1_relat_1(A_189),C_188)),A_189)
      | ~ r2_hidden(C_188,k1_relat_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_200,plain,(
    ! [C_211,A_212,B_213] :
      ( r2_hidden(k4_tarski(C_211,'#skF_5'(A_212,k1_relat_1(A_212),C_211)),B_213)
      | ~ r1_tarski(A_212,B_213)
      | ~ r2_hidden(C_211,k1_relat_1(A_212)) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_214,plain,(
    ! [C_211,B_213] :
      ( r2_hidden(k4_tarski(C_211,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_211)),B_213)
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_213)
      | ~ r2_hidden(C_211,k1_relat_1(k5_relat_1('#skF_17','#skF_16'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_200])).

tff(c_766,plain,(
    ! [C_294,B_295] :
      ( r2_hidden(k4_tarski(C_294,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_294)),B_295)
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_295)
      | ~ r2_hidden(C_294,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_214])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_786,plain,(
    ! [C_296,B_297] :
      ( r2_hidden(C_296,k1_relat_1(B_297))
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_297)
      | ~ r2_hidden(C_296,k1_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_766,c_10])).

tff(c_872,plain,(
    ! [C_162,B_297] :
      ( r2_hidden('#skF_15'('#skF_17',k2_relat_1('#skF_17'),C_162),k1_relat_1(B_297))
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_297)
      | ~ r2_hidden(C_162,k2_relat_1('#skF_17'))
      | ~ v1_funct_1('#skF_17')
      | ~ v1_relat_1('#skF_17') ) ),
    inference(resolution,[status(thm)],[c_44,c_786])).

tff(c_1155,plain,(
    ! [C_308,B_309] :
      ( r2_hidden('#skF_15'('#skF_17',k2_relat_1('#skF_17'),C_308),k1_relat_1(B_309))
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_309)
      | ~ r2_hidden(C_308,k2_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_872])).

tff(c_1168,plain,(
    ! [C_308] :
      ( r2_hidden('#skF_15'('#skF_17',k2_relat_1('#skF_17'),C_308),k1_relat_1('#skF_17'))
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_308,k2_relat_1('#skF_17')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1155])).

tff(c_1174,plain,(
    ! [C_308] :
      ( r2_hidden('#skF_15'('#skF_17',k2_relat_1('#skF_17'),C_308),k1_relat_1('#skF_17'))
      | ~ r2_hidden(C_308,k2_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_1168])).

tff(c_42,plain,(
    ! [A_126,C_162] :
      ( k1_funct_1(A_126,'#skF_15'(A_126,k2_relat_1(A_126),C_162)) = C_162
      | ~ r2_hidden(C_162,k2_relat_1(A_126))
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_219,plain,(
    ! [C_211,B_213] :
      ( r2_hidden(k4_tarski(C_211,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_211)),B_213)
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_213)
      | ~ r2_hidden(C_211,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_214])).

tff(c_74,plain,(
    v1_relat_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    ! [A_124,B_125] :
      ( v1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_155,plain,(
    ! [A_205,C_206] :
      ( r2_hidden('#skF_15'(A_205,k2_relat_1(A_205),C_206),k1_relat_1(A_205))
      | ~ r2_hidden(C_206,k2_relat_1(A_205))
      | ~ v1_funct_1(A_205)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_160,plain,(
    ! [C_206] :
      ( r2_hidden('#skF_15'(k5_relat_1('#skF_17','#skF_16'),k2_relat_1(k5_relat_1('#skF_17','#skF_16')),C_206),k1_relat_1('#skF_17'))
      | ~ r2_hidden(C_206,k2_relat_1(k5_relat_1('#skF_17','#skF_16')))
      | ~ v1_funct_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_155])).

tff(c_276,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16')) ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_279,plain,
    ( ~ v1_relat_1('#skF_16')
    | ~ v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_38,c_276])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_279])).

tff(c_285,plain,(
    v1_relat_1(k5_relat_1('#skF_17','#skF_16')) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_111,plain,(
    ! [C_188] :
      ( r2_hidden(k4_tarski(C_188,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_188)),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_188,k1_relat_1(k5_relat_1('#skF_17','#skF_16'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_103])).

tff(c_114,plain,(
    ! [C_188] :
      ( r2_hidden(k4_tarski(C_188,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_188)),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_188,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_111])).

tff(c_1845,plain,(
    ! [D_353,B_354,A_355,E_356] :
      ( r2_hidden(k4_tarski(D_353,'#skF_6'(D_353,B_354,A_355,E_356,k5_relat_1(A_355,B_354))),A_355)
      | ~ r2_hidden(k4_tarski(D_353,E_356),k5_relat_1(A_355,B_354))
      | ~ v1_relat_1(k5_relat_1(A_355,B_354))
      | ~ v1_relat_1(B_354)
      | ~ v1_relat_1(A_355) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ! [C_168,A_166,B_167] :
      ( k1_funct_1(C_168,A_166) = B_167
      | ~ r2_hidden(k4_tarski(A_166,B_167),C_168)
      | ~ v1_funct_1(C_168)
      | ~ v1_relat_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_7299,plain,(
    ! [D_658,B_659,A_660,E_661] :
      ( '#skF_6'(D_658,B_659,A_660,E_661,k5_relat_1(A_660,B_659)) = k1_funct_1(A_660,D_658)
      | ~ v1_funct_1(A_660)
      | ~ r2_hidden(k4_tarski(D_658,E_661),k5_relat_1(A_660,B_659))
      | ~ v1_relat_1(k5_relat_1(A_660,B_659))
      | ~ v1_relat_1(B_659)
      | ~ v1_relat_1(A_660) ) ),
    inference(resolution,[status(thm)],[c_1845,c_60])).

tff(c_7362,plain,(
    ! [C_188] :
      ( '#skF_6'(C_188,'#skF_16','#skF_17','#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_188),k5_relat_1('#skF_17','#skF_16')) = k1_funct_1('#skF_17',C_188)
      | ~ v1_funct_1('#skF_17')
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1('#skF_16')
      | ~ v1_relat_1('#skF_17')
      | ~ r2_hidden(C_188,k1_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_114,c_7299])).

tff(c_7395,plain,(
    ! [C_662] :
      ( '#skF_6'(C_662,'#skF_16','#skF_17','#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_662),k5_relat_1('#skF_17','#skF_16')) = k1_funct_1('#skF_17',C_662)
      | ~ r2_hidden(C_662,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_285,c_68,c_7362])).

tff(c_2409,plain,(
    ! [D_389,B_390,A_391,E_392] :
      ( r2_hidden(k4_tarski('#skF_6'(D_389,B_390,A_391,E_392,k5_relat_1(A_391,B_390)),E_392),B_390)
      | ~ r2_hidden(k4_tarski(D_389,E_392),k5_relat_1(A_391,B_390))
      | ~ v1_relat_1(k5_relat_1(A_391,B_390))
      | ~ v1_relat_1(B_390)
      | ~ v1_relat_1(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2448,plain,(
    ! [D_389,B_390,A_391,E_392] :
      ( r2_hidden('#skF_6'(D_389,B_390,A_391,E_392,k5_relat_1(A_391,B_390)),k1_relat_1(B_390))
      | ~ r2_hidden(k4_tarski(D_389,E_392),k5_relat_1(A_391,B_390))
      | ~ v1_relat_1(k5_relat_1(A_391,B_390))
      | ~ v1_relat_1(B_390)
      | ~ v1_relat_1(A_391) ) ),
    inference(resolution,[status(thm)],[c_2409,c_10])).

tff(c_7401,plain,(
    ! [C_662] :
      ( r2_hidden(k1_funct_1('#skF_17',C_662),k1_relat_1('#skF_16'))
      | ~ r2_hidden(k4_tarski(C_662,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_662)),k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1('#skF_16')
      | ~ v1_relat_1('#skF_17')
      | ~ r2_hidden(C_662,k1_relat_1('#skF_17')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7395,c_2448])).

tff(c_7977,plain,(
    ! [C_701] :
      ( r2_hidden(k1_funct_1('#skF_17',C_701),k1_relat_1('#skF_16'))
      | ~ r2_hidden(k4_tarski(C_701,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_701)),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_701,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_74,c_285,c_7401])).

tff(c_7981,plain,(
    ! [C_211] :
      ( r2_hidden(k1_funct_1('#skF_17',C_211),k1_relat_1('#skF_16'))
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_211,k1_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_219,c_7977])).

tff(c_7989,plain,(
    ! [C_702] :
      ( r2_hidden(k1_funct_1('#skF_17',C_702),k1_relat_1('#skF_16'))
      | ~ r2_hidden(C_702,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_7981])).

tff(c_8007,plain,(
    ! [C_162] :
      ( r2_hidden(C_162,k1_relat_1('#skF_16'))
      | ~ r2_hidden('#skF_15'('#skF_17',k2_relat_1('#skF_17'),C_162),k1_relat_1('#skF_17'))
      | ~ r2_hidden(C_162,k2_relat_1('#skF_17'))
      | ~ v1_funct_1('#skF_17')
      | ~ v1_relat_1('#skF_17') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_7989])).

tff(c_8098,plain,(
    ! [C_709] :
      ( r2_hidden(C_709,k1_relat_1('#skF_16'))
      | ~ r2_hidden('#skF_15'('#skF_17',k2_relat_1('#skF_17'),C_709),k1_relat_1('#skF_17'))
      | ~ r2_hidden(C_709,k2_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_8007])).

tff(c_8129,plain,(
    ! [C_710] :
      ( r2_hidden(C_710,k1_relat_1('#skF_16'))
      | ~ r2_hidden(C_710,k2_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_1174,c_8098])).

tff(c_8563,plain,(
    ! [B_711] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_17'),B_711),k1_relat_1('#skF_16'))
      | r1_tarski(k2_relat_1('#skF_17'),B_711) ) ),
    inference(resolution,[status(thm)],[c_6,c_8129])).

tff(c_8571,plain,(
    r1_tarski(k2_relat_1('#skF_17'),k1_relat_1('#skF_16')) ),
    inference(resolution,[status(thm)],[c_8563,c_4])).

tff(c_8579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_8571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.81/3.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.81/3.14  
% 9.81/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.81/3.14  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_17 > #skF_6 > #skF_3 > #skF_13 > #skF_16 > #skF_14 > #skF_12 > #skF_5 > #skF_11 > #skF_7 > #skF_9 > #skF_15 > #skF_2 > #skF_8 > #skF_1 > #skF_4 > #skF_10
% 9.81/3.14  
% 9.81/3.14  %Foreground sorts:
% 9.81/3.14  
% 9.81/3.14  
% 9.81/3.14  %Background operators:
% 9.81/3.14  
% 9.81/3.14  
% 9.81/3.14  %Foreground operators:
% 9.81/3.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.81/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.81/3.14  tff('#skF_17', type, '#skF_17': $i).
% 9.81/3.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.81/3.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.81/3.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.81/3.14  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i) > $i).
% 9.81/3.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.81/3.14  tff('#skF_13', type, '#skF_13': ($i * $i) > $i).
% 9.81/3.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.81/3.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.81/3.14  tff('#skF_16', type, '#skF_16': $i).
% 9.81/3.14  tff('#skF_14', type, '#skF_14': ($i * $i) > $i).
% 9.81/3.14  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 9.81/3.14  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 9.81/3.14  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 9.81/3.14  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.81/3.14  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.81/3.14  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 9.81/3.14  tff('#skF_15', type, '#skF_15': ($i * $i * $i) > $i).
% 9.81/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.81/3.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.81/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.81/3.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.81/3.14  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 9.81/3.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.81/3.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.81/3.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.81/3.14  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 9.81/3.14  
% 9.81/3.16  tff(f_103, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 9.81/3.16  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.81/3.16  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 9.81/3.16  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 9.81/3.16  tff(f_64, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 9.81/3.16  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 9.81/3.16  tff(f_89, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 9.81/3.16  tff(c_64, plain, (~r1_tarski(k2_relat_1('#skF_17'), k1_relat_1('#skF_16'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.81/3.16  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.16  tff(c_80, plain, (![A_172, B_173]: (r2_hidden('#skF_1'(A_172, B_173), A_172) | r1_tarski(A_172, B_173))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.16  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.16  tff(c_85, plain, (![A_172]: (r1_tarski(A_172, A_172))), inference(resolution, [status(thm)], [c_80, c_4])).
% 9.81/3.16  tff(c_66, plain, (k1_relat_1(k5_relat_1('#skF_17', '#skF_16'))=k1_relat_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.81/3.16  tff(c_70, plain, (v1_relat_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.81/3.16  tff(c_68, plain, (v1_funct_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.81/3.16  tff(c_44, plain, (![A_126, C_162]: (r2_hidden('#skF_15'(A_126, k2_relat_1(A_126), C_162), k1_relat_1(A_126)) | ~r2_hidden(C_162, k2_relat_1(A_126)) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.81/3.16  tff(c_103, plain, (![C_188, A_189]: (r2_hidden(k4_tarski(C_188, '#skF_5'(A_189, k1_relat_1(A_189), C_188)), A_189) | ~r2_hidden(C_188, k1_relat_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.81/3.16  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.81/3.16  tff(c_200, plain, (![C_211, A_212, B_213]: (r2_hidden(k4_tarski(C_211, '#skF_5'(A_212, k1_relat_1(A_212), C_211)), B_213) | ~r1_tarski(A_212, B_213) | ~r2_hidden(C_211, k1_relat_1(A_212)))), inference(resolution, [status(thm)], [c_103, c_2])).
% 9.81/3.16  tff(c_214, plain, (![C_211, B_213]: (r2_hidden(k4_tarski(C_211, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_211)), B_213) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_213) | ~r2_hidden(C_211, k1_relat_1(k5_relat_1('#skF_17', '#skF_16'))))), inference(superposition, [status(thm), theory('equality')], [c_66, c_200])).
% 9.81/3.16  tff(c_766, plain, (![C_294, B_295]: (r2_hidden(k4_tarski(C_294, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_294)), B_295) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_295) | ~r2_hidden(C_294, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_214])).
% 9.81/3.16  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.81/3.16  tff(c_786, plain, (![C_296, B_297]: (r2_hidden(C_296, k1_relat_1(B_297)) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_297) | ~r2_hidden(C_296, k1_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_766, c_10])).
% 9.81/3.16  tff(c_872, plain, (![C_162, B_297]: (r2_hidden('#skF_15'('#skF_17', k2_relat_1('#skF_17'), C_162), k1_relat_1(B_297)) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_297) | ~r2_hidden(C_162, k2_relat_1('#skF_17')) | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17'))), inference(resolution, [status(thm)], [c_44, c_786])).
% 9.81/3.16  tff(c_1155, plain, (![C_308, B_309]: (r2_hidden('#skF_15'('#skF_17', k2_relat_1('#skF_17'), C_308), k1_relat_1(B_309)) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_309) | ~r2_hidden(C_308, k2_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_872])).
% 9.81/3.16  tff(c_1168, plain, (![C_308]: (r2_hidden('#skF_15'('#skF_17', k2_relat_1('#skF_17'), C_308), k1_relat_1('#skF_17')) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_308, k2_relat_1('#skF_17')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1155])).
% 9.81/3.16  tff(c_1174, plain, (![C_308]: (r2_hidden('#skF_15'('#skF_17', k2_relat_1('#skF_17'), C_308), k1_relat_1('#skF_17')) | ~r2_hidden(C_308, k2_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_1168])).
% 9.81/3.16  tff(c_42, plain, (![A_126, C_162]: (k1_funct_1(A_126, '#skF_15'(A_126, k2_relat_1(A_126), C_162))=C_162 | ~r2_hidden(C_162, k2_relat_1(A_126)) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.81/3.16  tff(c_219, plain, (![C_211, B_213]: (r2_hidden(k4_tarski(C_211, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_211)), B_213) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_213) | ~r2_hidden(C_211, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_214])).
% 9.81/3.16  tff(c_74, plain, (v1_relat_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.81/3.16  tff(c_38, plain, (![A_124, B_125]: (v1_relat_1(k5_relat_1(A_124, B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.81/3.16  tff(c_155, plain, (![A_205, C_206]: (r2_hidden('#skF_15'(A_205, k2_relat_1(A_205), C_206), k1_relat_1(A_205)) | ~r2_hidden(C_206, k2_relat_1(A_205)) | ~v1_funct_1(A_205) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.81/3.16  tff(c_160, plain, (![C_206]: (r2_hidden('#skF_15'(k5_relat_1('#skF_17', '#skF_16'), k2_relat_1(k5_relat_1('#skF_17', '#skF_16')), C_206), k1_relat_1('#skF_17')) | ~r2_hidden(C_206, k2_relat_1(k5_relat_1('#skF_17', '#skF_16'))) | ~v1_funct_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_155])).
% 9.81/3.16  tff(c_276, plain, (~v1_relat_1(k5_relat_1('#skF_17', '#skF_16'))), inference(splitLeft, [status(thm)], [c_160])).
% 9.81/3.16  tff(c_279, plain, (~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_38, c_276])).
% 9.81/3.16  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_279])).
% 9.81/3.16  tff(c_285, plain, (v1_relat_1(k5_relat_1('#skF_17', '#skF_16'))), inference(splitRight, [status(thm)], [c_160])).
% 9.81/3.16  tff(c_111, plain, (![C_188]: (r2_hidden(k4_tarski(C_188, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_188)), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_188, k1_relat_1(k5_relat_1('#skF_17', '#skF_16'))))), inference(superposition, [status(thm), theory('equality')], [c_66, c_103])).
% 9.81/3.16  tff(c_114, plain, (![C_188]: (r2_hidden(k4_tarski(C_188, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_188)), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_188, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_111])).
% 9.81/3.16  tff(c_1845, plain, (![D_353, B_354, A_355, E_356]: (r2_hidden(k4_tarski(D_353, '#skF_6'(D_353, B_354, A_355, E_356, k5_relat_1(A_355, B_354))), A_355) | ~r2_hidden(k4_tarski(D_353, E_356), k5_relat_1(A_355, B_354)) | ~v1_relat_1(k5_relat_1(A_355, B_354)) | ~v1_relat_1(B_354) | ~v1_relat_1(A_355))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.81/3.16  tff(c_60, plain, (![C_168, A_166, B_167]: (k1_funct_1(C_168, A_166)=B_167 | ~r2_hidden(k4_tarski(A_166, B_167), C_168) | ~v1_funct_1(C_168) | ~v1_relat_1(C_168))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.81/3.16  tff(c_7299, plain, (![D_658, B_659, A_660, E_661]: ('#skF_6'(D_658, B_659, A_660, E_661, k5_relat_1(A_660, B_659))=k1_funct_1(A_660, D_658) | ~v1_funct_1(A_660) | ~r2_hidden(k4_tarski(D_658, E_661), k5_relat_1(A_660, B_659)) | ~v1_relat_1(k5_relat_1(A_660, B_659)) | ~v1_relat_1(B_659) | ~v1_relat_1(A_660))), inference(resolution, [status(thm)], [c_1845, c_60])).
% 9.81/3.16  tff(c_7362, plain, (![C_188]: ('#skF_6'(C_188, '#skF_16', '#skF_17', '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_188), k5_relat_1('#skF_17', '#skF_16'))=k1_funct_1('#skF_17', C_188) | ~v1_funct_1('#skF_17') | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17') | ~r2_hidden(C_188, k1_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_114, c_7299])).
% 9.81/3.16  tff(c_7395, plain, (![C_662]: ('#skF_6'(C_662, '#skF_16', '#skF_17', '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_662), k5_relat_1('#skF_17', '#skF_16'))=k1_funct_1('#skF_17', C_662) | ~r2_hidden(C_662, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_285, c_68, c_7362])).
% 9.81/3.16  tff(c_2409, plain, (![D_389, B_390, A_391, E_392]: (r2_hidden(k4_tarski('#skF_6'(D_389, B_390, A_391, E_392, k5_relat_1(A_391, B_390)), E_392), B_390) | ~r2_hidden(k4_tarski(D_389, E_392), k5_relat_1(A_391, B_390)) | ~v1_relat_1(k5_relat_1(A_391, B_390)) | ~v1_relat_1(B_390) | ~v1_relat_1(A_391))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.81/3.16  tff(c_2448, plain, (![D_389, B_390, A_391, E_392]: (r2_hidden('#skF_6'(D_389, B_390, A_391, E_392, k5_relat_1(A_391, B_390)), k1_relat_1(B_390)) | ~r2_hidden(k4_tarski(D_389, E_392), k5_relat_1(A_391, B_390)) | ~v1_relat_1(k5_relat_1(A_391, B_390)) | ~v1_relat_1(B_390) | ~v1_relat_1(A_391))), inference(resolution, [status(thm)], [c_2409, c_10])).
% 9.81/3.16  tff(c_7401, plain, (![C_662]: (r2_hidden(k1_funct_1('#skF_17', C_662), k1_relat_1('#skF_16')) | ~r2_hidden(k4_tarski(C_662, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_662)), k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17') | ~r2_hidden(C_662, k1_relat_1('#skF_17')))), inference(superposition, [status(thm), theory('equality')], [c_7395, c_2448])).
% 9.81/3.16  tff(c_7977, plain, (![C_701]: (r2_hidden(k1_funct_1('#skF_17', C_701), k1_relat_1('#skF_16')) | ~r2_hidden(k4_tarski(C_701, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_701)), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_701, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_74, c_285, c_7401])).
% 9.81/3.16  tff(c_7981, plain, (![C_211]: (r2_hidden(k1_funct_1('#skF_17', C_211), k1_relat_1('#skF_16')) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_211, k1_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_219, c_7977])).
% 9.81/3.16  tff(c_7989, plain, (![C_702]: (r2_hidden(k1_funct_1('#skF_17', C_702), k1_relat_1('#skF_16')) | ~r2_hidden(C_702, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_7981])).
% 9.81/3.16  tff(c_8007, plain, (![C_162]: (r2_hidden(C_162, k1_relat_1('#skF_16')) | ~r2_hidden('#skF_15'('#skF_17', k2_relat_1('#skF_17'), C_162), k1_relat_1('#skF_17')) | ~r2_hidden(C_162, k2_relat_1('#skF_17')) | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_7989])).
% 9.81/3.16  tff(c_8098, plain, (![C_709]: (r2_hidden(C_709, k1_relat_1('#skF_16')) | ~r2_hidden('#skF_15'('#skF_17', k2_relat_1('#skF_17'), C_709), k1_relat_1('#skF_17')) | ~r2_hidden(C_709, k2_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_8007])).
% 9.81/3.16  tff(c_8129, plain, (![C_710]: (r2_hidden(C_710, k1_relat_1('#skF_16')) | ~r2_hidden(C_710, k2_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_1174, c_8098])).
% 9.81/3.16  tff(c_8563, plain, (![B_711]: (r2_hidden('#skF_1'(k2_relat_1('#skF_17'), B_711), k1_relat_1('#skF_16')) | r1_tarski(k2_relat_1('#skF_17'), B_711))), inference(resolution, [status(thm)], [c_6, c_8129])).
% 9.81/3.16  tff(c_8571, plain, (r1_tarski(k2_relat_1('#skF_17'), k1_relat_1('#skF_16'))), inference(resolution, [status(thm)], [c_8563, c_4])).
% 9.81/3.16  tff(c_8579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_8571])).
% 9.81/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.81/3.16  
% 9.81/3.16  Inference rules
% 9.81/3.16  ----------------------
% 9.81/3.16  #Ref     : 0
% 9.81/3.16  #Sup     : 1922
% 9.81/3.16  #Fact    : 0
% 9.81/3.16  #Define  : 0
% 9.81/3.16  #Split   : 4
% 9.81/3.16  #Chain   : 0
% 9.81/3.16  #Close   : 0
% 9.81/3.16  
% 9.81/3.16  Ordering : KBO
% 9.81/3.16  
% 9.81/3.16  Simplification rules
% 9.81/3.16  ----------------------
% 9.81/3.16  #Subsume      : 317
% 9.81/3.16  #Demod        : 524
% 9.81/3.16  #Tautology    : 206
% 9.81/3.16  #SimpNegUnit  : 1
% 9.81/3.16  #BackRed      : 0
% 9.81/3.16  
% 9.81/3.16  #Partial instantiations: 0
% 9.81/3.16  #Strategies tried      : 1
% 9.81/3.16  
% 9.81/3.16  Timing (in seconds)
% 9.81/3.16  ----------------------
% 9.81/3.16  Preprocessing        : 0.34
% 9.81/3.16  Parsing              : 0.16
% 9.81/3.16  CNF conversion       : 0.04
% 9.81/3.16  Main loop            : 2.06
% 9.81/3.16  Inferencing          : 0.63
% 9.81/3.16  Reduction            : 0.45
% 9.81/3.16  Demodulation         : 0.29
% 9.81/3.16  BG Simplification    : 0.08
% 9.81/3.16  Subsumption          : 0.74
% 9.81/3.16  Abstraction          : 0.12
% 9.81/3.16  MUC search           : 0.00
% 9.81/3.16  Cooper               : 0.00
% 9.81/3.16  Total                : 2.43
% 9.81/3.16  Index Insertion      : 0.00
% 9.81/3.16  Index Deletion       : 0.00
% 9.81/3.16  Index Matching       : 0.00
% 9.81/3.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

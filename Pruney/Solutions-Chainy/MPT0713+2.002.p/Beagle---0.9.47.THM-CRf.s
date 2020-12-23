%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:35 EST 2020

% Result     : Theorem 7.06s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :   58 (  92 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  124 ( 249 expanded)
%              Number of equality atoms :   51 (  90 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_9,B_11] :
      ( k9_relat_1(A_9,k1_tarski(B_11)) = k11_relat_1(A_9,B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    k2_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3'))) != k1_tarski(k1_funct_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_tarski(k1_funct_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_32])).

tff(c_86,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_tarski(k1_funct_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_84])).

tff(c_89,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k11_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_91,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k11_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_89])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_238,plain,(
    ! [A_63,C_64] :
      ( r2_hidden(k4_tarski(A_63,k1_funct_1(C_64,A_63)),C_64)
      | ~ r2_hidden(A_63,k1_relat_1(C_64))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    ! [B_15,C_16,A_14] :
      ( r2_hidden(B_15,k11_relat_1(C_16,A_14))
      | ~ r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_269,plain,(
    ! [C_64,A_63] :
      ( r2_hidden(k1_funct_1(C_64,A_63),k11_relat_1(C_64,A_63))
      | ~ r2_hidden(A_63,k1_relat_1(C_64))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_238,c_24])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden(k4_tarski(A_14,B_15),C_16)
      | ~ r2_hidden(B_15,k11_relat_1(C_16,A_14))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    ! [C_47,A_48,B_49] :
      ( k1_funct_1(C_47,A_48) = B_49
      | ~ r2_hidden(k4_tarski(A_48,B_49),C_47)
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,(
    ! [C_53,A_54,B_55] :
      ( k1_funct_1(C_53,A_54) = B_55
      | ~ v1_funct_1(C_53)
      | ~ r2_hidden(B_55,k11_relat_1(C_53,A_54))
      | ~ v1_relat_1(C_53) ) ),
    inference(resolution,[status(thm)],[c_22,c_132])).

tff(c_506,plain,(
    ! [A_95,C_96,A_97] :
      ( '#skF_2'(A_95,k11_relat_1(C_96,A_97)) = k1_funct_1(C_96,A_97)
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96)
      | '#skF_1'(A_95,k11_relat_1(C_96,A_97)) = A_95
      | k1_tarski(A_95) = k11_relat_1(C_96,A_97) ) ),
    inference(resolution,[status(thm)],[c_12,c_158])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_517,plain,(
    ! [A_95,C_96,A_97] :
      ( '#skF_1'(A_95,k11_relat_1(C_96,A_97)) = A_95
      | k1_funct_1(C_96,A_97) != A_95
      | k1_tarski(A_95) = k11_relat_1(C_96,A_97)
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96)
      | '#skF_1'(A_95,k11_relat_1(C_96,A_97)) = A_95
      | k1_tarski(A_95) = k11_relat_1(C_96,A_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_8])).

tff(c_1593,plain,(
    ! [C_179,A_180,A_181] :
      ( k1_funct_1(C_179,A_180) != A_181
      | ~ v1_funct_1(C_179)
      | ~ v1_relat_1(C_179)
      | k1_tarski(A_181) = k11_relat_1(C_179,A_180)
      | '#skF_1'(A_181,k11_relat_1(C_179,A_180)) = A_181 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_517])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_171,plain,(
    ! [A_1,C_53,A_54] :
      ( '#skF_2'(A_1,k11_relat_1(C_53,A_54)) = k1_funct_1(C_53,A_54)
      | ~ v1_funct_1(C_53)
      | ~ v1_relat_1(C_53)
      | ~ r2_hidden('#skF_1'(A_1,k11_relat_1(C_53,A_54)),k11_relat_1(C_53,A_54))
      | k1_tarski(A_1) = k11_relat_1(C_53,A_54) ) ),
    inference(resolution,[status(thm)],[c_10,c_158])).

tff(c_3987,plain,(
    ! [A_307,C_308,A_309] :
      ( '#skF_2'(A_307,k11_relat_1(C_308,A_309)) = k1_funct_1(C_308,A_309)
      | ~ v1_funct_1(C_308)
      | ~ v1_relat_1(C_308)
      | ~ r2_hidden(A_307,k11_relat_1(C_308,A_309))
      | k1_tarski(A_307) = k11_relat_1(C_308,A_309)
      | k1_funct_1(C_308,A_309) != A_307
      | ~ v1_funct_1(C_308)
      | ~ v1_relat_1(C_308)
      | k1_tarski(A_307) = k11_relat_1(C_308,A_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1593,c_171])).

tff(c_4056,plain,(
    ! [C_310,A_311] :
      ( '#skF_2'(k1_funct_1(C_310,A_311),k11_relat_1(C_310,A_311)) = k1_funct_1(C_310,A_311)
      | k1_tarski(k1_funct_1(C_310,A_311)) = k11_relat_1(C_310,A_311)
      | ~ r2_hidden(A_311,k1_relat_1(C_310))
      | ~ v1_funct_1(C_310)
      | ~ v1_relat_1(C_310) ) ),
    inference(resolution,[status(thm)],[c_269,c_3987])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1666,plain,(
    ! [A_182,C_183,A_184] :
      ( ~ r2_hidden(A_182,k11_relat_1(C_183,A_184))
      | '#skF_2'(A_182,k11_relat_1(C_183,A_184)) != A_182
      | k1_tarski(A_182) = k11_relat_1(C_183,A_184)
      | k1_funct_1(C_183,A_184) != A_182
      | ~ v1_funct_1(C_183)
      | ~ v1_relat_1(C_183)
      | k1_tarski(A_182) = k11_relat_1(C_183,A_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1593,c_6])).

tff(c_1701,plain,(
    ! [C_64,A_63] :
      ( '#skF_2'(k1_funct_1(C_64,A_63),k11_relat_1(C_64,A_63)) != k1_funct_1(C_64,A_63)
      | k1_tarski(k1_funct_1(C_64,A_63)) = k11_relat_1(C_64,A_63)
      | ~ r2_hidden(A_63,k1_relat_1(C_64))
      | ~ v1_funct_1(C_64)
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_269,c_1666])).

tff(c_4106,plain,(
    ! [C_312,A_313] :
      ( k1_tarski(k1_funct_1(C_312,A_313)) = k11_relat_1(C_312,A_313)
      | ~ r2_hidden(A_313,k1_relat_1(C_312))
      | ~ v1_funct_1(C_312)
      | ~ v1_relat_1(C_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4056,c_1701])).

tff(c_4140,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_4106])).

tff(c_4152,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_4140])).

tff(c_4154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_4152])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.06/2.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.57  
% 7.06/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.58  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.06/2.58  
% 7.06/2.58  %Foreground sorts:
% 7.06/2.58  
% 7.06/2.58  
% 7.06/2.58  %Background operators:
% 7.06/2.58  
% 7.06/2.58  
% 7.06/2.58  %Foreground operators:
% 7.06/2.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.06/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.06/2.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.06/2.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.06/2.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.06/2.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.06/2.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.06/2.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.06/2.58  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 7.06/2.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.06/2.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.06/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.06/2.58  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.06/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.06/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.06/2.58  tff('#skF_4', type, '#skF_4': $i).
% 7.06/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.06/2.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.06/2.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.06/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.06/2.58  
% 7.06/2.60  tff(f_70, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 7.06/2.60  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 7.06/2.60  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 7.06/2.60  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.06/2.60  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 7.06/2.60  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.06/2.60  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.06/2.60  tff(c_18, plain, (![A_9, B_11]: (k9_relat_1(A_9, k1_tarski(B_11))=k11_relat_1(A_9, B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.06/2.60  tff(c_20, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.06/2.60  tff(c_32, plain, (k2_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3')))!=k1_tarski(k1_funct_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.06/2.60  tff(c_84, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_tarski(k1_funct_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_32])).
% 7.06/2.60  tff(c_86, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_tarski(k1_funct_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_84])).
% 7.06/2.60  tff(c_89, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k11_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18, c_86])).
% 7.06/2.60  tff(c_91, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k11_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_89])).
% 7.06/2.60  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.06/2.60  tff(c_34, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.06/2.60  tff(c_238, plain, (![A_63, C_64]: (r2_hidden(k4_tarski(A_63, k1_funct_1(C_64, A_63)), C_64) | ~r2_hidden(A_63, k1_relat_1(C_64)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.06/2.60  tff(c_24, plain, (![B_15, C_16, A_14]: (r2_hidden(B_15, k11_relat_1(C_16, A_14)) | ~r2_hidden(k4_tarski(A_14, B_15), C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.06/2.60  tff(c_269, plain, (![C_64, A_63]: (r2_hidden(k1_funct_1(C_64, A_63), k11_relat_1(C_64, A_63)) | ~r2_hidden(A_63, k1_relat_1(C_64)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_238, c_24])).
% 7.06/2.60  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.06/2.60  tff(c_22, plain, (![A_14, B_15, C_16]: (r2_hidden(k4_tarski(A_14, B_15), C_16) | ~r2_hidden(B_15, k11_relat_1(C_16, A_14)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.06/2.60  tff(c_132, plain, (![C_47, A_48, B_49]: (k1_funct_1(C_47, A_48)=B_49 | ~r2_hidden(k4_tarski(A_48, B_49), C_47) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.06/2.60  tff(c_158, plain, (![C_53, A_54, B_55]: (k1_funct_1(C_53, A_54)=B_55 | ~v1_funct_1(C_53) | ~r2_hidden(B_55, k11_relat_1(C_53, A_54)) | ~v1_relat_1(C_53))), inference(resolution, [status(thm)], [c_22, c_132])).
% 7.06/2.60  tff(c_506, plain, (![A_95, C_96, A_97]: ('#skF_2'(A_95, k11_relat_1(C_96, A_97))=k1_funct_1(C_96, A_97) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96) | '#skF_1'(A_95, k11_relat_1(C_96, A_97))=A_95 | k1_tarski(A_95)=k11_relat_1(C_96, A_97))), inference(resolution, [status(thm)], [c_12, c_158])).
% 7.06/2.60  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.06/2.60  tff(c_517, plain, (![A_95, C_96, A_97]: ('#skF_1'(A_95, k11_relat_1(C_96, A_97))=A_95 | k1_funct_1(C_96, A_97)!=A_95 | k1_tarski(A_95)=k11_relat_1(C_96, A_97) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96) | '#skF_1'(A_95, k11_relat_1(C_96, A_97))=A_95 | k1_tarski(A_95)=k11_relat_1(C_96, A_97))), inference(superposition, [status(thm), theory('equality')], [c_506, c_8])).
% 7.06/2.60  tff(c_1593, plain, (![C_179, A_180, A_181]: (k1_funct_1(C_179, A_180)!=A_181 | ~v1_funct_1(C_179) | ~v1_relat_1(C_179) | k1_tarski(A_181)=k11_relat_1(C_179, A_180) | '#skF_1'(A_181, k11_relat_1(C_179, A_180))=A_181)), inference(factorization, [status(thm), theory('equality')], [c_517])).
% 7.06/2.60  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.06/2.60  tff(c_171, plain, (![A_1, C_53, A_54]: ('#skF_2'(A_1, k11_relat_1(C_53, A_54))=k1_funct_1(C_53, A_54) | ~v1_funct_1(C_53) | ~v1_relat_1(C_53) | ~r2_hidden('#skF_1'(A_1, k11_relat_1(C_53, A_54)), k11_relat_1(C_53, A_54)) | k1_tarski(A_1)=k11_relat_1(C_53, A_54))), inference(resolution, [status(thm)], [c_10, c_158])).
% 7.06/2.60  tff(c_3987, plain, (![A_307, C_308, A_309]: ('#skF_2'(A_307, k11_relat_1(C_308, A_309))=k1_funct_1(C_308, A_309) | ~v1_funct_1(C_308) | ~v1_relat_1(C_308) | ~r2_hidden(A_307, k11_relat_1(C_308, A_309)) | k1_tarski(A_307)=k11_relat_1(C_308, A_309) | k1_funct_1(C_308, A_309)!=A_307 | ~v1_funct_1(C_308) | ~v1_relat_1(C_308) | k1_tarski(A_307)=k11_relat_1(C_308, A_309))), inference(superposition, [status(thm), theory('equality')], [c_1593, c_171])).
% 7.06/2.60  tff(c_4056, plain, (![C_310, A_311]: ('#skF_2'(k1_funct_1(C_310, A_311), k11_relat_1(C_310, A_311))=k1_funct_1(C_310, A_311) | k1_tarski(k1_funct_1(C_310, A_311))=k11_relat_1(C_310, A_311) | ~r2_hidden(A_311, k1_relat_1(C_310)) | ~v1_funct_1(C_310) | ~v1_relat_1(C_310))), inference(resolution, [status(thm)], [c_269, c_3987])).
% 7.06/2.60  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.06/2.60  tff(c_1666, plain, (![A_182, C_183, A_184]: (~r2_hidden(A_182, k11_relat_1(C_183, A_184)) | '#skF_2'(A_182, k11_relat_1(C_183, A_184))!=A_182 | k1_tarski(A_182)=k11_relat_1(C_183, A_184) | k1_funct_1(C_183, A_184)!=A_182 | ~v1_funct_1(C_183) | ~v1_relat_1(C_183) | k1_tarski(A_182)=k11_relat_1(C_183, A_184))), inference(superposition, [status(thm), theory('equality')], [c_1593, c_6])).
% 7.06/2.60  tff(c_1701, plain, (![C_64, A_63]: ('#skF_2'(k1_funct_1(C_64, A_63), k11_relat_1(C_64, A_63))!=k1_funct_1(C_64, A_63) | k1_tarski(k1_funct_1(C_64, A_63))=k11_relat_1(C_64, A_63) | ~r2_hidden(A_63, k1_relat_1(C_64)) | ~v1_funct_1(C_64) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_269, c_1666])).
% 7.06/2.60  tff(c_4106, plain, (![C_312, A_313]: (k1_tarski(k1_funct_1(C_312, A_313))=k11_relat_1(C_312, A_313) | ~r2_hidden(A_313, k1_relat_1(C_312)) | ~v1_funct_1(C_312) | ~v1_relat_1(C_312))), inference(superposition, [status(thm), theory('equality')], [c_4056, c_1701])).
% 7.06/2.60  tff(c_4140, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_4106])).
% 7.06/2.60  tff(c_4152, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_4140])).
% 7.06/2.60  tff(c_4154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_4152])).
% 7.06/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.60  
% 7.06/2.60  Inference rules
% 7.06/2.60  ----------------------
% 7.06/2.60  #Ref     : 0
% 7.06/2.60  #Sup     : 1039
% 7.06/2.60  #Fact    : 4
% 7.06/2.60  #Define  : 0
% 7.28/2.60  #Split   : 1
% 7.28/2.60  #Chain   : 0
% 7.28/2.60  #Close   : 0
% 7.28/2.60  
% 7.28/2.60  Ordering : KBO
% 7.28/2.60  
% 7.28/2.60  Simplification rules
% 7.28/2.60  ----------------------
% 7.28/2.60  #Subsume      : 165
% 7.28/2.60  #Demod        : 32
% 7.28/2.60  #Tautology    : 209
% 7.28/2.60  #SimpNegUnit  : 1
% 7.28/2.60  #BackRed      : 0
% 7.28/2.60  
% 7.28/2.60  #Partial instantiations: 0
% 7.28/2.60  #Strategies tried      : 1
% 7.28/2.60  
% 7.28/2.60  Timing (in seconds)
% 7.28/2.60  ----------------------
% 7.28/2.60  Preprocessing        : 0.29
% 7.28/2.60  Parsing              : 0.15
% 7.28/2.60  CNF conversion       : 0.02
% 7.28/2.60  Main loop            : 1.50
% 7.28/2.60  Inferencing          : 0.48
% 7.28/2.60  Reduction            : 0.31
% 7.28/2.60  Demodulation         : 0.21
% 7.28/2.60  BG Simplification    : 0.08
% 7.28/2.60  Subsumption          : 0.52
% 7.28/2.61  Abstraction          : 0.11
% 7.28/2.61  MUC search           : 0.00
% 7.28/2.61  Cooper               : 0.00
% 7.28/2.61  Total                : 1.84
% 7.28/2.61  Index Insertion      : 0.00
% 7.28/2.61  Index Deletion       : 0.00
% 7.28/2.61  Index Matching       : 0.00
% 7.28/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:35 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 201 expanded)
%              Number of leaves         :   28 (  85 expanded)
%              Depth                    :   17
%              Number of atoms          :  119 ( 520 expanded)
%              Number of equality atoms :   57 ( 189 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r2_hidden(A,k1_relat_1(B))
         => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_38,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_196,plain,(
    ! [B_61,A_62] :
      ( r2_hidden(k4_tarski(B_61,k1_funct_1(A_62,B_61)),A_62)
      | ~ r2_hidden(B_61,k1_relat_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [B_18,C_19,A_17] :
      ( r2_hidden(B_18,k11_relat_1(C_19,A_17))
      | ~ r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_209,plain,(
    ! [A_62,B_61] :
      ( r2_hidden(k1_funct_1(A_62,B_61),k11_relat_1(A_62,B_61))
      | ~ r2_hidden(B_61,k1_relat_1(A_62))
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_196,c_26])).

tff(c_20,plain,(
    ! [A_12,B_14] :
      ( k9_relat_1(A_12,k1_tarski(B_14)) = k11_relat_1(A_12,B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [B_36,A_37] :
      ( k2_relat_1(k7_relat_1(B_36,A_37)) = k9_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36,plain,(
    k2_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3'))) != k1_tarski(k1_funct_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_92,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_tarski(k1_funct_1('#skF_4','#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_36])).

tff(c_98,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_3')) != k1_tarski(k1_funct_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_92])).

tff(c_102,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k11_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_104,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_3')) != k11_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_12,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k4_tarski(A_17,B_18),C_19)
      | ~ r2_hidden(B_18,k11_relat_1(C_19,A_17))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_217,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_funct_1(A_65,B_66) = C_67
      | ~ r2_hidden(k4_tarski(B_66,C_67),A_65)
      | ~ r2_hidden(B_66,k1_relat_1(A_65))
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_243,plain,(
    ! [C_70,A_71,B_72] :
      ( k1_funct_1(C_70,A_71) = B_72
      | ~ r2_hidden(A_71,k1_relat_1(C_70))
      | ~ v1_funct_1(C_70)
      | ~ r2_hidden(B_72,k11_relat_1(C_70,A_71))
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_24,c_217])).

tff(c_259,plain,(
    ! [B_72] :
      ( k1_funct_1('#skF_4','#skF_3') = B_72
      | ~ v1_funct_1('#skF_4')
      | ~ r2_hidden(B_72,k11_relat_1('#skF_4','#skF_3'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_243])).

tff(c_268,plain,(
    ! [B_73] :
      ( k1_funct_1('#skF_4','#skF_3') = B_73
      | ~ r2_hidden(B_73,k11_relat_1('#skF_4','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_259])).

tff(c_396,plain,(
    ! [A_84] :
      ( '#skF_2'(A_84,k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
      | '#skF_1'(A_84,k11_relat_1('#skF_4','#skF_3')) = A_84
      | k1_tarski(A_84) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_268])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( '#skF_1'(A_1,B_2) = A_1
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_407,plain,(
    ! [A_84] :
      ( '#skF_1'(A_84,k11_relat_1('#skF_4','#skF_3')) = A_84
      | k1_funct_1('#skF_4','#skF_3') != A_84
      | k1_tarski(A_84) = k11_relat_1('#skF_4','#skF_3')
      | '#skF_1'(A_84,k11_relat_1('#skF_4','#skF_3')) = A_84
      | k1_tarski(A_84) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_8])).

tff(c_607,plain,(
    ! [A_110] :
      ( k1_funct_1('#skF_4','#skF_3') != A_110
      | k1_tarski(A_110) = k11_relat_1('#skF_4','#skF_3')
      | '#skF_1'(A_110,k11_relat_1('#skF_4','#skF_3')) = A_110 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_407])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | '#skF_2'(A_1,B_2) != A_1
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_674,plain,(
    ! [A_118] :
      ( ~ r2_hidden(A_118,k11_relat_1('#skF_4','#skF_3'))
      | '#skF_2'(A_118,k11_relat_1('#skF_4','#skF_3')) != A_118
      | k1_tarski(A_118) = k11_relat_1('#skF_4','#skF_3')
      | k1_funct_1('#skF_4','#skF_3') != A_118
      | k1_tarski(A_118) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_607,c_6])).

tff(c_682,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) != k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_209,c_674])).

tff(c_704,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) != k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_682])).

tff(c_705,plain,(
    '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) != k1_funct_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_704])).

tff(c_296,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
      | '#skF_1'(A_1,k11_relat_1('#skF_4','#skF_3')) = A_1
      | k1_tarski(A_1) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_12,c_268])).

tff(c_750,plain,
    ( '#skF_1'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_705])).

tff(c_753,plain,(
    '#skF_1'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_750])).

tff(c_10,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r2_hidden('#skF_2'(A_1,B_2),B_2)
      | k1_tarski(A_1) = B_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_294,plain,(
    ! [A_1] :
      ( '#skF_2'(A_1,k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
      | ~ r2_hidden('#skF_1'(A_1,k11_relat_1('#skF_4','#skF_3')),k11_relat_1('#skF_4','#skF_3'))
      | k1_tarski(A_1) = k11_relat_1('#skF_4','#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_268])).

tff(c_760,plain,
    ( '#skF_2'(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) = k1_funct_1('#skF_4','#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3'))
    | k1_tarski(k1_funct_1('#skF_4','#skF_3')) = k11_relat_1('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_294])).

tff(c_773,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_705,c_760])).

tff(c_782,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_209,c_773])).

tff(c_786,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.52  
% 3.28/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.52  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.28/1.52  
% 3.28/1.52  %Foreground sorts:
% 3.28/1.52  
% 3.28/1.52  
% 3.28/1.52  %Background operators:
% 3.28/1.52  
% 3.28/1.52  
% 3.28/1.52  %Foreground operators:
% 3.28/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.28/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.28/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.28/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.52  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.28/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.28/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.28/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.28/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.52  
% 3.31/1.54  tff(f_80, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 3.31/1.54  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 3.31/1.54  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t204_relat_1)).
% 3.31/1.54  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.31/1.54  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.31/1.54  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.31/1.54  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.54  tff(c_40, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.54  tff(c_38, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.54  tff(c_196, plain, (![B_61, A_62]: (r2_hidden(k4_tarski(B_61, k1_funct_1(A_62, B_61)), A_62) | ~r2_hidden(B_61, k1_relat_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.31/1.54  tff(c_26, plain, (![B_18, C_19, A_17]: (r2_hidden(B_18, k11_relat_1(C_19, A_17)) | ~r2_hidden(k4_tarski(A_17, B_18), C_19) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.31/1.54  tff(c_209, plain, (![A_62, B_61]: (r2_hidden(k1_funct_1(A_62, B_61), k11_relat_1(A_62, B_61)) | ~r2_hidden(B_61, k1_relat_1(A_62)) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_196, c_26])).
% 3.31/1.54  tff(c_20, plain, (![A_12, B_14]: (k9_relat_1(A_12, k1_tarski(B_14))=k11_relat_1(A_12, B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.31/1.54  tff(c_86, plain, (![B_36, A_37]: (k2_relat_1(k7_relat_1(B_36, A_37))=k9_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.31/1.54  tff(c_36, plain, (k2_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3')))!=k1_tarski(k1_funct_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.31/1.54  tff(c_92, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_tarski(k1_funct_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_86, c_36])).
% 3.31/1.54  tff(c_98, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_3'))!=k1_tarski(k1_funct_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_92])).
% 3.31/1.54  tff(c_102, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k11_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_20, c_98])).
% 3.31/1.54  tff(c_104, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_3'))!=k11_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 3.31/1.54  tff(c_12, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.54  tff(c_24, plain, (![A_17, B_18, C_19]: (r2_hidden(k4_tarski(A_17, B_18), C_19) | ~r2_hidden(B_18, k11_relat_1(C_19, A_17)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.31/1.54  tff(c_217, plain, (![A_65, B_66, C_67]: (k1_funct_1(A_65, B_66)=C_67 | ~r2_hidden(k4_tarski(B_66, C_67), A_65) | ~r2_hidden(B_66, k1_relat_1(A_65)) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.31/1.54  tff(c_243, plain, (![C_70, A_71, B_72]: (k1_funct_1(C_70, A_71)=B_72 | ~r2_hidden(A_71, k1_relat_1(C_70)) | ~v1_funct_1(C_70) | ~r2_hidden(B_72, k11_relat_1(C_70, A_71)) | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_24, c_217])).
% 3.31/1.54  tff(c_259, plain, (![B_72]: (k1_funct_1('#skF_4', '#skF_3')=B_72 | ~v1_funct_1('#skF_4') | ~r2_hidden(B_72, k11_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_243])).
% 3.31/1.54  tff(c_268, plain, (![B_73]: (k1_funct_1('#skF_4', '#skF_3')=B_73 | ~r2_hidden(B_73, k11_relat_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_259])).
% 3.31/1.54  tff(c_396, plain, (![A_84]: ('#skF_2'(A_84, k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | '#skF_1'(A_84, k11_relat_1('#skF_4', '#skF_3'))=A_84 | k1_tarski(A_84)=k11_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_268])).
% 3.31/1.54  tff(c_8, plain, (![A_1, B_2]: ('#skF_1'(A_1, B_2)=A_1 | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.54  tff(c_407, plain, (![A_84]: ('#skF_1'(A_84, k11_relat_1('#skF_4', '#skF_3'))=A_84 | k1_funct_1('#skF_4', '#skF_3')!=A_84 | k1_tarski(A_84)=k11_relat_1('#skF_4', '#skF_3') | '#skF_1'(A_84, k11_relat_1('#skF_4', '#skF_3'))=A_84 | k1_tarski(A_84)=k11_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_396, c_8])).
% 3.31/1.54  tff(c_607, plain, (![A_110]: (k1_funct_1('#skF_4', '#skF_3')!=A_110 | k1_tarski(A_110)=k11_relat_1('#skF_4', '#skF_3') | '#skF_1'(A_110, k11_relat_1('#skF_4', '#skF_3'))=A_110)), inference(factorization, [status(thm), theory('equality')], [c_407])).
% 3.31/1.54  tff(c_6, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | '#skF_2'(A_1, B_2)!=A_1 | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.54  tff(c_674, plain, (![A_118]: (~r2_hidden(A_118, k11_relat_1('#skF_4', '#skF_3')) | '#skF_2'(A_118, k11_relat_1('#skF_4', '#skF_3'))!=A_118 | k1_tarski(A_118)=k11_relat_1('#skF_4', '#skF_3') | k1_funct_1('#skF_4', '#skF_3')!=A_118 | k1_tarski(A_118)=k11_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_607, c_6])).
% 3.31/1.54  tff(c_682, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))!=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3') | ~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_209, c_674])).
% 3.31/1.54  tff(c_704, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))!=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_682])).
% 3.31/1.54  tff(c_705, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))!=k1_funct_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_104, c_704])).
% 3.31/1.54  tff(c_296, plain, (![A_1]: ('#skF_2'(A_1, k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | '#skF_1'(A_1, k11_relat_1('#skF_4', '#skF_3'))=A_1 | k1_tarski(A_1)=k11_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_268])).
% 3.31/1.54  tff(c_750, plain, ('#skF_1'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_296, c_705])).
% 3.31/1.54  tff(c_753, plain, ('#skF_1'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_104, c_750])).
% 3.31/1.54  tff(c_10, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r2_hidden('#skF_2'(A_1, B_2), B_2) | k1_tarski(A_1)=B_2)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.54  tff(c_294, plain, (![A_1]: ('#skF_2'(A_1, k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | ~r2_hidden('#skF_1'(A_1, k11_relat_1('#skF_4', '#skF_3')), k11_relat_1('#skF_4', '#skF_3')) | k1_tarski(A_1)=k11_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_268])).
% 3.31/1.54  tff(c_760, plain, ('#skF_2'(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))=k1_funct_1('#skF_4', '#skF_3') | ~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3')) | k1_tarski(k1_funct_1('#skF_4', '#skF_3'))=k11_relat_1('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_753, c_294])).
% 3.31/1.54  tff(c_773, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_104, c_705, c_760])).
% 3.31/1.54  tff(c_782, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_209, c_773])).
% 3.31/1.54  tff(c_786, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_782])).
% 3.31/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.54  
% 3.31/1.54  Inference rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Ref     : 0
% 3.31/1.54  #Sup     : 153
% 3.31/1.54  #Fact    : 2
% 3.31/1.54  #Define  : 0
% 3.31/1.54  #Split   : 1
% 3.31/1.54  #Chain   : 0
% 3.31/1.54  #Close   : 0
% 3.31/1.54  
% 3.31/1.54  Ordering : KBO
% 3.31/1.54  
% 3.31/1.54  Simplification rules
% 3.31/1.54  ----------------------
% 3.31/1.54  #Subsume      : 16
% 3.31/1.54  #Demod        : 19
% 3.31/1.54  #Tautology    : 39
% 3.31/1.54  #SimpNegUnit  : 6
% 3.31/1.54  #BackRed      : 0
% 3.31/1.54  
% 3.31/1.54  #Partial instantiations: 0
% 3.31/1.54  #Strategies tried      : 1
% 3.31/1.54  
% 3.31/1.54  Timing (in seconds)
% 3.31/1.54  ----------------------
% 3.31/1.54  Preprocessing        : 0.31
% 3.31/1.54  Parsing              : 0.16
% 3.31/1.54  CNF conversion       : 0.02
% 3.31/1.54  Main loop            : 0.47
% 3.31/1.54  Inferencing          : 0.18
% 3.31/1.54  Reduction            : 0.12
% 3.31/1.54  Demodulation         : 0.08
% 3.31/1.54  BG Simplification    : 0.03
% 3.31/1.54  Subsumption          : 0.11
% 3.31/1.54  Abstraction          : 0.04
% 3.31/1.54  MUC search           : 0.00
% 3.31/1.54  Cooper               : 0.00
% 3.31/1.54  Total                : 0.81
% 3.31/1.54  Index Insertion      : 0.00
% 3.31/1.54  Index Deletion       : 0.00
% 3.31/1.54  Index Matching       : 0.00
% 3.31/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

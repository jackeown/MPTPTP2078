%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:31 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   67 (  92 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 142 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_92,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_50,axiom,(
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

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    ! [A_29] : k2_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    ! [A_29] : k1_relat_1(k6_relat_1(A_29)) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_102,plain,(
    ! [A_43] :
      ( k9_relat_1(A_43,k1_relat_1(A_43)) = k2_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_111,plain,(
    ! [A_29] :
      ( k9_relat_1(k6_relat_1(A_29),A_29) = k2_relat_1(k6_relat_1(A_29))
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_102])).

tff(c_115,plain,(
    ! [A_29] : k9_relat_1(k6_relat_1(A_29),A_29) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_111])).

tff(c_239,plain,(
    ! [B_72,A_73] :
      ( r1_xboole_0(k1_relat_1(B_72),A_73)
      | k9_relat_1(B_72,A_73) != k1_xboole_0
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_244,plain,(
    ! [A_29,A_73] :
      ( r1_xboole_0(A_29,A_73)
      | k9_relat_1(k6_relat_1(A_29),A_73) != k1_xboole_0
      | ~ v1_relat_1(k6_relat_1(A_29)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_239])).

tff(c_248,plain,(
    ! [A_74,A_75] :
      ( r1_xboole_0(A_74,A_75)
      | k9_relat_1(k6_relat_1(A_74),A_75) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_244])).

tff(c_265,plain,(
    ! [A_76] :
      ( r1_xboole_0(A_76,A_76)
      | k1_xboole_0 != A_76 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_248])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_270,plain,(
    ! [C_77,A_78] :
      ( ~ r2_hidden(C_77,A_78)
      | k1_xboole_0 != A_78 ) ),
    inference(resolution,[status(thm)],[c_265,c_8])).

tff(c_317,plain,(
    ! [A_81,B_82] :
      ( k1_xboole_0 != A_81
      | r1_tarski(A_81,B_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_270])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    ! [A_19,B_21] :
      ( k9_relat_1(A_19,k1_tarski(B_21)) = k11_relat_1(A_19,B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_155,plain,(
    ! [B_62,A_63] :
      ( k2_relat_1(k7_relat_1(B_62,A_63)) = k9_relat_1(B_62,A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',k1_tarski('#skF_3'))),k1_tarski(k1_funct_1('#skF_4','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_161,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4',k1_tarski('#skF_3')),k1_tarski(k1_funct_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_50])).

tff(c_167,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4',k1_tarski('#skF_3')),k1_tarski(k1_funct_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_161])).

tff(c_202,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_167])).

tff(c_204,plain,(
    ~ r1_tarski(k11_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_202])).

tff(c_329,plain,(
    k11_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_317,c_204])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( r2_hidden(A_27,k1_relat_1(B_28))
      | k11_relat_1(B_28,A_27) = k1_xboole_0
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_457,plain,(
    ! [B_98,A_99] :
      ( k1_tarski(k1_funct_1(B_98,A_99)) = k11_relat_1(B_98,A_99)
      | ~ r2_hidden(A_99,k1_relat_1(B_98))
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1424,plain,(
    ! [B_184,A_185] :
      ( k1_tarski(k1_funct_1(B_184,A_185)) = k11_relat_1(B_184,A_185)
      | ~ v1_funct_1(B_184)
      | k11_relat_1(B_184,A_185) = k1_xboole_0
      | ~ v1_relat_1(B_184) ) ),
    inference(resolution,[status(thm)],[c_36,c_457])).

tff(c_1445,plain,
    ( ~ r1_tarski(k11_relat_1('#skF_4','#skF_3'),k11_relat_1('#skF_4','#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | k11_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_204])).

tff(c_1472,plain,(
    k11_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_18,c_1445])).

tff(c_1474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_1472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.09/1.52  
% 3.09/1.52  %Foreground sorts:
% 3.09/1.52  
% 3.09/1.52  
% 3.09/1.52  %Background operators:
% 3.09/1.52  
% 3.09/1.52  
% 3.09/1.52  %Foreground operators:
% 3.09/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.09/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.09/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.52  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.09/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.09/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.09/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.09/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.09/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.52  
% 3.43/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.43/1.54  tff(f_96, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.43/1.54  tff(f_92, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.43/1.54  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.43/1.54  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 3.43/1.54  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.43/1.54  tff(f_111, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 3.43/1.54  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 3.43/1.54  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.43/1.54  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.43/1.54  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 3.43/1.54  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 3.43/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.43/1.54  tff(c_44, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.43/1.54  tff(c_42, plain, (![A_29]: (k2_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.43/1.54  tff(c_40, plain, (![A_29]: (k1_relat_1(k6_relat_1(A_29))=A_29)), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.43/1.54  tff(c_102, plain, (![A_43]: (k9_relat_1(A_43, k1_relat_1(A_43))=k2_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.43/1.54  tff(c_111, plain, (![A_29]: (k9_relat_1(k6_relat_1(A_29), A_29)=k2_relat_1(k6_relat_1(A_29)) | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_102])).
% 3.43/1.54  tff(c_115, plain, (![A_29]: (k9_relat_1(k6_relat_1(A_29), A_29)=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_111])).
% 3.43/1.54  tff(c_239, plain, (![B_72, A_73]: (r1_xboole_0(k1_relat_1(B_72), A_73) | k9_relat_1(B_72, A_73)!=k1_xboole_0 | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.43/1.54  tff(c_244, plain, (![A_29, A_73]: (r1_xboole_0(A_29, A_73) | k9_relat_1(k6_relat_1(A_29), A_73)!=k1_xboole_0 | ~v1_relat_1(k6_relat_1(A_29)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_239])).
% 3.43/1.54  tff(c_248, plain, (![A_74, A_75]: (r1_xboole_0(A_74, A_75) | k9_relat_1(k6_relat_1(A_74), A_75)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_244])).
% 3.43/1.54  tff(c_265, plain, (![A_76]: (r1_xboole_0(A_76, A_76) | k1_xboole_0!=A_76)), inference(superposition, [status(thm), theory('equality')], [c_115, c_248])).
% 3.43/1.54  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.43/1.54  tff(c_270, plain, (![C_77, A_78]: (~r2_hidden(C_77, A_78) | k1_xboole_0!=A_78)), inference(resolution, [status(thm)], [c_265, c_8])).
% 3.43/1.54  tff(c_317, plain, (![A_81, B_82]: (k1_xboole_0!=A_81 | r1_tarski(A_81, B_82))), inference(resolution, [status(thm)], [c_6, c_270])).
% 3.43/1.54  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.43/1.54  tff(c_26, plain, (![A_19, B_21]: (k9_relat_1(A_19, k1_tarski(B_21))=k11_relat_1(A_19, B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.43/1.54  tff(c_155, plain, (![B_62, A_63]: (k2_relat_1(k7_relat_1(B_62, A_63))=k9_relat_1(B_62, A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.43/1.54  tff(c_50, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', k1_tarski('#skF_3'))), k1_tarski(k1_funct_1('#skF_4', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.43/1.54  tff(c_161, plain, (~r1_tarski(k9_relat_1('#skF_4', k1_tarski('#skF_3')), k1_tarski(k1_funct_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_155, c_50])).
% 3.43/1.54  tff(c_167, plain, (~r1_tarski(k9_relat_1('#skF_4', k1_tarski('#skF_3')), k1_tarski(k1_funct_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_161])).
% 3.43/1.54  tff(c_202, plain, (~r1_tarski(k11_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26, c_167])).
% 3.43/1.54  tff(c_204, plain, (~r1_tarski(k11_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_202])).
% 3.43/1.54  tff(c_329, plain, (k11_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_317, c_204])).
% 3.43/1.54  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.43/1.54  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.43/1.54  tff(c_36, plain, (![A_27, B_28]: (r2_hidden(A_27, k1_relat_1(B_28)) | k11_relat_1(B_28, A_27)=k1_xboole_0 | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.43/1.54  tff(c_457, plain, (![B_98, A_99]: (k1_tarski(k1_funct_1(B_98, A_99))=k11_relat_1(B_98, A_99) | ~r2_hidden(A_99, k1_relat_1(B_98)) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.43/1.54  tff(c_1424, plain, (![B_184, A_185]: (k1_tarski(k1_funct_1(B_184, A_185))=k11_relat_1(B_184, A_185) | ~v1_funct_1(B_184) | k11_relat_1(B_184, A_185)=k1_xboole_0 | ~v1_relat_1(B_184))), inference(resolution, [status(thm)], [c_36, c_457])).
% 3.43/1.54  tff(c_1445, plain, (~r1_tarski(k11_relat_1('#skF_4', '#skF_3'), k11_relat_1('#skF_4', '#skF_3')) | ~v1_funct_1('#skF_4') | k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1424, c_204])).
% 3.43/1.54  tff(c_1472, plain, (k11_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_18, c_1445])).
% 3.43/1.54  tff(c_1474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_329, c_1472])).
% 3.43/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.43/1.54  
% 3.43/1.54  Inference rules
% 3.43/1.54  ----------------------
% 3.43/1.54  #Ref     : 1
% 3.43/1.54  #Sup     : 297
% 3.43/1.54  #Fact    : 0
% 3.43/1.54  #Define  : 0
% 3.43/1.54  #Split   : 2
% 3.43/1.54  #Chain   : 0
% 3.43/1.54  #Close   : 0
% 3.43/1.54  
% 3.43/1.54  Ordering : KBO
% 3.43/1.54  
% 3.43/1.54  Simplification rules
% 3.43/1.54  ----------------------
% 3.43/1.54  #Subsume      : 80
% 3.43/1.54  #Demod        : 144
% 3.43/1.54  #Tautology    : 102
% 3.43/1.54  #SimpNegUnit  : 3
% 3.43/1.54  #BackRed      : 0
% 3.43/1.54  
% 3.43/1.54  #Partial instantiations: 0
% 3.43/1.54  #Strategies tried      : 1
% 3.43/1.54  
% 3.43/1.54  Timing (in seconds)
% 3.43/1.54  ----------------------
% 3.43/1.54  Preprocessing        : 0.32
% 3.43/1.54  Parsing              : 0.16
% 3.43/1.54  CNF conversion       : 0.02
% 3.43/1.54  Main loop            : 0.45
% 3.43/1.54  Inferencing          : 0.17
% 3.43/1.54  Reduction            : 0.14
% 3.43/1.54  Demodulation         : 0.10
% 3.43/1.54  BG Simplification    : 0.02
% 3.43/1.54  Subsumption          : 0.09
% 3.43/1.54  Abstraction          : 0.02
% 3.43/1.54  MUC search           : 0.00
% 3.43/1.54  Cooper               : 0.00
% 3.43/1.54  Total                : 0.80
% 3.43/1.54  Index Insertion      : 0.00
% 3.43/1.54  Index Deletion       : 0.00
% 3.43/1.54  Index Matching       : 0.00
% 3.43/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

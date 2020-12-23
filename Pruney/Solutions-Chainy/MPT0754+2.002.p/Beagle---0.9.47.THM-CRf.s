%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:30 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.41s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 101 expanded)
%              Number of leaves         :   28 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 178 expanded)
%              Number of equality atoms :   24 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => ! [C] :
            ( ( v1_relat_1(C)
              & v5_relat_1(C,A)
              & v1_funct_1(C)
              & v5_ordinal1(C) )
           => ( v1_relat_1(C)
              & v5_relat_1(C,B)
              & v1_funct_1(C)
              & v5_ordinal1(C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ! [B_28,A_27] :
      ( r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v5_relat_1(B_28,A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k4_xboole_0(A_41,C_42),B_43)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_692,plain,(
    ! [A_74,C_75,B_76] :
      ( k4_xboole_0(k4_xboole_0(A_74,C_75),B_76) = k1_xboole_0
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(resolution,[status(thm)],[c_115,c_6])).

tff(c_785,plain,(
    ! [A_77,C_78] :
      ( k4_xboole_0(A_77,C_78) = k1_xboole_0
      | ~ r1_tarski(A_77,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_10])).

tff(c_809,plain,(
    ! [A_3,C_78] :
      ( k4_xboole_0(A_3,C_78) = k1_xboole_0
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_785])).

tff(c_828,plain,(
    ! [A_79,C_80] :
      ( k4_xboole_0(A_79,C_80) = k1_xboole_0
      | k1_xboole_0 != A_79 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_809])).

tff(c_961,plain,(
    ! [B_10] : k3_xboole_0(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_828])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_160,plain,(
    ! [A_47] : k4_xboole_0(A_47,A_47) = k3_xboole_0(A_47,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_131])).

tff(c_288,plain,(
    ! [A_62] : k4_xboole_0(A_62,k3_xboole_0(A_62,k1_xboole_0)) = k3_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_12])).

tff(c_310,plain,(
    ! [A_1] : k4_xboole_0(A_1,k3_xboole_0(k1_xboole_0,A_1)) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_288])).

tff(c_965,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = k3_xboole_0(A_1,A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_310])).

tff(c_966,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_965])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_713,plain,(
    ! [A_74,C_75,B_76] :
      ( k4_xboole_0(k4_xboole_0(A_74,C_75),k1_xboole_0) = k3_xboole_0(k4_xboole_0(A_74,C_75),B_76)
      | ~ r1_tarski(A_74,B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_12])).

tff(c_3743,plain,(
    ! [A_170,C_171,B_172] :
      ( k3_xboole_0(k4_xboole_0(A_170,C_171),B_172) = k4_xboole_0(A_170,C_171)
      | ~ r1_tarski(A_170,B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_713])).

tff(c_8,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_213,plain,(
    ! [A_49,B_50,B_51] :
      ( r1_tarski(k3_xboole_0(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_8])).

tff(c_228,plain,(
    ! [B_2,A_1,B_51] :
      ( r1_tarski(k3_xboole_0(B_2,A_1),B_51)
      | ~ r1_tarski(A_1,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_213])).

tff(c_25390,plain,(
    ! [A_435,C_436,B_437,B_438] :
      ( r1_tarski(k4_xboole_0(A_435,C_436),B_437)
      | ~ r1_tarski(B_438,B_437)
      | ~ r1_tarski(A_435,B_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3743,c_228])).

tff(c_25436,plain,(
    ! [A_439,C_440] :
      ( r1_tarski(k4_xboole_0(A_439,C_440),'#skF_2')
      | ~ r1_tarski(A_439,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_25390])).

tff(c_25553,plain,(
    ! [A_441,B_442] :
      ( r1_tarski(k3_xboole_0(A_441,B_442),'#skF_2')
      | ~ r1_tarski(A_441,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_25436])).

tff(c_25754,plain,(
    ! [A_443] :
      ( r1_tarski(A_443,'#skF_2')
      | ~ r1_tarski(A_443,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_966,c_25553])).

tff(c_24,plain,(
    ! [B_28,A_27] :
      ( v5_relat_1(B_28,A_27)
      | ~ r1_tarski(k2_relat_1(B_28),A_27)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28054,plain,(
    ! [B_458] :
      ( v5_relat_1(B_458,'#skF_2')
      | ~ v1_relat_1(B_458)
      | ~ r1_tarski(k2_relat_1(B_458),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_25754,c_24])).

tff(c_28073,plain,(
    ! [B_459] :
      ( v5_relat_1(B_459,'#skF_2')
      | ~ v5_relat_1(B_459,'#skF_1')
      | ~ v1_relat_1(B_459) ) ),
    inference(resolution,[status(thm)],[c_26,c_28054])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v5_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,
    ( ~ v5_ordinal1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ~ v5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_30,c_28])).

tff(c_28082,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28073,c_40])).

tff(c_28088,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28082])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:07 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/4.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/4.44  
% 10.38/4.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.38/4.44  %$ v5_relat_1 > r1_tarski > v5_ordinal1 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.38/4.44  
% 10.38/4.44  %Foreground sorts:
% 10.38/4.44  
% 10.38/4.44  
% 10.38/4.44  %Background operators:
% 10.38/4.44  
% 10.38/4.44  
% 10.38/4.44  %Foreground operators:
% 10.38/4.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.38/4.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/4.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.38/4.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.38/4.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.38/4.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.38/4.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.38/4.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.38/4.44  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 10.38/4.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.38/4.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.38/4.44  tff('#skF_2', type, '#skF_2': $i).
% 10.38/4.44  tff('#skF_3', type, '#skF_3': $i).
% 10.38/4.44  tff('#skF_1', type, '#skF_1': $i).
% 10.38/4.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.38/4.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.38/4.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/4.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.38/4.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/4.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.38/4.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.38/4.44  
% 10.41/4.46  tff(f_75, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (![C]: ((((v1_relat_1(C) & v5_relat_1(C, A)) & v1_funct_1(C)) & v5_ordinal1(C)) => (((v1_relat_1(C) & v5_relat_1(C, B)) & v1_funct_1(C)) & v5_ordinal1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_ordinal1)).
% 10.41/4.46  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 10.41/4.46  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.41/4.46  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.41/4.46  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.41/4.46  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 10.41/4.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.41/4.46  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.41/4.46  tff(c_34, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.41/4.46  tff(c_26, plain, (![B_28, A_27]: (r1_tarski(k2_relat_1(B_28), A_27) | ~v5_relat_1(B_28, A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.41/4.46  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.41/4.46  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.41/4.46  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.41/4.46  tff(c_115, plain, (![A_41, C_42, B_43]: (r1_tarski(k4_xboole_0(A_41, C_42), B_43) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.41/4.46  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.41/4.46  tff(c_692, plain, (![A_74, C_75, B_76]: (k4_xboole_0(k4_xboole_0(A_74, C_75), B_76)=k1_xboole_0 | ~r1_tarski(A_74, B_76))), inference(resolution, [status(thm)], [c_115, c_6])).
% 10.41/4.46  tff(c_785, plain, (![A_77, C_78]: (k4_xboole_0(A_77, C_78)=k1_xboole_0 | ~r1_tarski(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_692, c_10])).
% 10.41/4.46  tff(c_809, plain, (![A_3, C_78]: (k4_xboole_0(A_3, C_78)=k1_xboole_0 | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_785])).
% 10.41/4.46  tff(c_828, plain, (![A_79, C_80]: (k4_xboole_0(A_79, C_80)=k1_xboole_0 | k1_xboole_0!=A_79)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_809])).
% 10.41/4.46  tff(c_961, plain, (![B_10]: (k3_xboole_0(k1_xboole_0, B_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_828])).
% 10.41/4.46  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.41/4.46  tff(c_131, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.41/4.46  tff(c_160, plain, (![A_47]: (k4_xboole_0(A_47, A_47)=k3_xboole_0(A_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_131])).
% 10.41/4.46  tff(c_288, plain, (![A_62]: (k4_xboole_0(A_62, k3_xboole_0(A_62, k1_xboole_0))=k3_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_160, c_12])).
% 10.41/4.46  tff(c_310, plain, (![A_1]: (k4_xboole_0(A_1, k3_xboole_0(k1_xboole_0, A_1))=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_288])).
% 10.41/4.46  tff(c_965, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=k3_xboole_0(A_1, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_961, c_310])).
% 10.41/4.46  tff(c_966, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_965])).
% 10.41/4.46  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.41/4.46  tff(c_713, plain, (![A_74, C_75, B_76]: (k4_xboole_0(k4_xboole_0(A_74, C_75), k1_xboole_0)=k3_xboole_0(k4_xboole_0(A_74, C_75), B_76) | ~r1_tarski(A_74, B_76))), inference(superposition, [status(thm), theory('equality')], [c_692, c_12])).
% 10.41/4.46  tff(c_3743, plain, (![A_170, C_171, B_172]: (k3_xboole_0(k4_xboole_0(A_170, C_171), B_172)=k4_xboole_0(A_170, C_171) | ~r1_tarski(A_170, B_172))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_713])).
% 10.41/4.46  tff(c_8, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.41/4.46  tff(c_213, plain, (![A_49, B_50, B_51]: (r1_tarski(k3_xboole_0(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51))), inference(superposition, [status(thm), theory('equality')], [c_131, c_8])).
% 10.41/4.46  tff(c_228, plain, (![B_2, A_1, B_51]: (r1_tarski(k3_xboole_0(B_2, A_1), B_51) | ~r1_tarski(A_1, B_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_213])).
% 10.41/4.46  tff(c_25390, plain, (![A_435, C_436, B_437, B_438]: (r1_tarski(k4_xboole_0(A_435, C_436), B_437) | ~r1_tarski(B_438, B_437) | ~r1_tarski(A_435, B_438))), inference(superposition, [status(thm), theory('equality')], [c_3743, c_228])).
% 10.41/4.46  tff(c_25436, plain, (![A_439, C_440]: (r1_tarski(k4_xboole_0(A_439, C_440), '#skF_2') | ~r1_tarski(A_439, '#skF_1'))), inference(resolution, [status(thm)], [c_38, c_25390])).
% 10.41/4.46  tff(c_25553, plain, (![A_441, B_442]: (r1_tarski(k3_xboole_0(A_441, B_442), '#skF_2') | ~r1_tarski(A_441, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_25436])).
% 10.41/4.46  tff(c_25754, plain, (![A_443]: (r1_tarski(A_443, '#skF_2') | ~r1_tarski(A_443, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_966, c_25553])).
% 10.41/4.46  tff(c_24, plain, (![B_28, A_27]: (v5_relat_1(B_28, A_27) | ~r1_tarski(k2_relat_1(B_28), A_27) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.41/4.46  tff(c_28054, plain, (![B_458]: (v5_relat_1(B_458, '#skF_2') | ~v1_relat_1(B_458) | ~r1_tarski(k2_relat_1(B_458), '#skF_1'))), inference(resolution, [status(thm)], [c_25754, c_24])).
% 10.41/4.46  tff(c_28073, plain, (![B_459]: (v5_relat_1(B_459, '#skF_2') | ~v5_relat_1(B_459, '#skF_1') | ~v1_relat_1(B_459))), inference(resolution, [status(thm)], [c_26, c_28054])).
% 10.41/4.46  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.41/4.46  tff(c_30, plain, (v5_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.41/4.46  tff(c_28, plain, (~v5_ordinal1('#skF_3') | ~v1_funct_1('#skF_3') | ~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.41/4.46  tff(c_40, plain, (~v5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_30, c_28])).
% 10.41/4.46  tff(c_28082, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28073, c_40])).
% 10.41/4.46  tff(c_28088, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28082])).
% 10.41/4.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.41/4.46  
% 10.41/4.46  Inference rules
% 10.41/4.46  ----------------------
% 10.41/4.46  #Ref     : 3
% 10.41/4.46  #Sup     : 7126
% 10.41/4.46  #Fact    : 0
% 10.41/4.46  #Define  : 0
% 10.41/4.46  #Split   : 12
% 10.41/4.46  #Chain   : 0
% 10.41/4.46  #Close   : 0
% 10.41/4.46  
% 10.41/4.46  Ordering : KBO
% 10.41/4.46  
% 10.41/4.46  Simplification rules
% 10.41/4.46  ----------------------
% 10.41/4.46  #Subsume      : 3817
% 10.41/4.46  #Demod        : 3631
% 10.41/4.46  #Tautology    : 2150
% 10.41/4.46  #SimpNegUnit  : 369
% 10.41/4.46  #BackRed      : 123
% 10.41/4.46  
% 10.41/4.46  #Partial instantiations: 0
% 10.41/4.46  #Strategies tried      : 1
% 10.41/4.46  
% 10.41/4.46  Timing (in seconds)
% 10.41/4.46  ----------------------
% 10.41/4.46  Preprocessing        : 0.33
% 10.41/4.46  Parsing              : 0.18
% 10.41/4.46  CNF conversion       : 0.02
% 10.41/4.46  Main loop            : 3.29
% 10.41/4.46  Inferencing          : 0.69
% 10.41/4.46  Reduction            : 1.41
% 10.41/4.46  Demodulation         : 1.14
% 10.41/4.46  BG Simplification    : 0.07
% 10.41/4.46  Subsumption          : 0.97
% 10.41/4.46  Abstraction          : 0.12
% 10.41/4.46  MUC search           : 0.00
% 10.41/4.46  Cooper               : 0.00
% 10.41/4.46  Total                : 3.66
% 10.41/4.46  Index Insertion      : 0.00
% 10.41/4.46  Index Deletion       : 0.00
% 10.41/4.46  Index Matching       : 0.00
% 10.41/4.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:11 EST 2020

% Result     : Theorem 4.40s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 122 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_20,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_124,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_139,plain,(
    ! [B_36,A_37] : k1_setfam_1(k2_tarski(B_36,A_37)) = k3_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_124])).

tff(c_24,plain,(
    ! [A_11,B_12] : k1_setfam_1(k2_tarski(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_24])).

tff(c_48,plain,(
    r2_hidden('#skF_4',k3_xboole_0(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_162,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_relat_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_48])).

tff(c_217,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,A_46)
      | ~ r2_hidden(D_45,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_227,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_162,c_217])).

tff(c_52,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    ! [A_16] : v1_relat_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    ! [A_16] : v1_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    ! [A_21,C_25] :
      ( k1_funct_1(k6_relat_1(A_21),C_25) = C_25
      | ~ r2_hidden(C_25,A_21)
      | ~ v1_funct_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_56,plain,(
    ! [A_21,C_25] :
      ( k1_funct_1(k6_relat_1(A_21),C_25) = C_25
      | ~ r2_hidden(C_25,A_21)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_58,plain,(
    ! [A_21,C_25] :
      ( k1_funct_1(k6_relat_1(A_21),C_25) = C_25
      | ~ r2_hidden(C_25,A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_44,plain,(
    ! [A_21] :
      ( k1_relat_1(k6_relat_1(A_21)) = A_21
      | ~ v1_funct_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_21] :
      ( k1_relat_1(k6_relat_1(A_21)) = A_21
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_60,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_54])).

tff(c_466,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_funct_1(k5_relat_1(B_82,C_83),A_84) = k1_funct_1(C_83,k1_funct_1(B_82,A_84))
      | ~ r2_hidden(A_84,k1_relat_1(B_82))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_502,plain,(
    ! [A_21,C_83,A_84] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_21),C_83),A_84) = k1_funct_1(C_83,k1_funct_1(k6_relat_1(A_21),A_84))
      | ~ r2_hidden(A_84,A_21)
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_466])).

tff(c_894,plain,(
    ! [A_114,C_115,A_116] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_114),C_115),A_116) = k1_funct_1(C_115,k1_funct_1(k6_relat_1(A_114),A_116))
      | ~ r2_hidden(A_116,A_114)
      | ~ v1_funct_1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_502])).

tff(c_990,plain,(
    ! [B_123,A_124,A_125] :
      ( k1_funct_1(B_123,k1_funct_1(k6_relat_1(A_124),A_125)) = k1_funct_1(k7_relat_1(B_123,A_124),A_125)
      | ~ r2_hidden(A_125,A_124)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_894])).

tff(c_2051,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_funct_1(k7_relat_1(B_205,A_206),C_207) = k1_funct_1(B_205,C_207)
      | ~ r2_hidden(C_207,A_206)
      | ~ v1_funct_1(B_205)
      | ~ v1_relat_1(B_205)
      | ~ v1_relat_1(B_205)
      | ~ r2_hidden(C_207,A_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_990])).

tff(c_46,plain,(
    k1_funct_1(k7_relat_1('#skF_6','#skF_5'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2069,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2051,c_46])).

tff(c_2086,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_52,c_50,c_2069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:02:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.40/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.78  
% 4.40/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.40/1.79  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.40/1.79  
% 4.40/1.79  %Foreground sorts:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Background operators:
% 4.40/1.79  
% 4.40/1.79  
% 4.40/1.79  %Foreground operators:
% 4.40/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.40/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.40/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.40/1.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.40/1.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.40/1.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.40/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.40/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.40/1.79  tff('#skF_5', type, '#skF_5': $i).
% 4.40/1.79  tff('#skF_6', type, '#skF_6': $i).
% 4.40/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.40/1.79  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.40/1.79  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.40/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.40/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.40/1.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.40/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.40/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.40/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.40/1.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.40/1.79  
% 4.48/1.80  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.48/1.80  tff(f_40, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.48/1.80  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 4.48/1.80  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.48/1.80  tff(f_52, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.48/1.80  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 4.48/1.80  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.48/1.80  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 4.48/1.80  tff(c_20, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.48/1.80  tff(c_124, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.48/1.80  tff(c_139, plain, (![B_36, A_37]: (k1_setfam_1(k2_tarski(B_36, A_37))=k3_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_20, c_124])).
% 4.48/1.80  tff(c_24, plain, (![A_11, B_12]: (k1_setfam_1(k2_tarski(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.48/1.80  tff(c_145, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_139, c_24])).
% 4.48/1.80  tff(c_48, plain, (r2_hidden('#skF_4', k3_xboole_0(k1_relat_1('#skF_6'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_162, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_48])).
% 4.48/1.80  tff(c_217, plain, (![D_45, A_46, B_47]: (r2_hidden(D_45, A_46) | ~r2_hidden(D_45, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.48/1.80  tff(c_227, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_162, c_217])).
% 4.48/1.80  tff(c_52, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_32, plain, (![A_16]: (v1_relat_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.48/1.80  tff(c_34, plain, (![A_16]: (v1_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.48/1.80  tff(c_42, plain, (![A_21, C_25]: (k1_funct_1(k6_relat_1(A_21), C_25)=C_25 | ~r2_hidden(C_25, A_21) | ~v1_funct_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.48/1.80  tff(c_56, plain, (![A_21, C_25]: (k1_funct_1(k6_relat_1(A_21), C_25)=C_25 | ~r2_hidden(C_25, A_21) | ~v1_relat_1(k6_relat_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 4.48/1.80  tff(c_58, plain, (![A_21, C_25]: (k1_funct_1(k6_relat_1(A_21), C_25)=C_25 | ~r2_hidden(C_25, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56])).
% 4.48/1.80  tff(c_30, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.48/1.80  tff(c_44, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21 | ~v1_funct_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.48/1.80  tff(c_54, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21 | ~v1_relat_1(k6_relat_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 4.48/1.80  tff(c_60, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_54])).
% 4.48/1.80  tff(c_466, plain, (![B_82, C_83, A_84]: (k1_funct_1(k5_relat_1(B_82, C_83), A_84)=k1_funct_1(C_83, k1_funct_1(B_82, A_84)) | ~r2_hidden(A_84, k1_relat_1(B_82)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.48/1.80  tff(c_502, plain, (![A_21, C_83, A_84]: (k1_funct_1(k5_relat_1(k6_relat_1(A_21), C_83), A_84)=k1_funct_1(C_83, k1_funct_1(k6_relat_1(A_21), A_84)) | ~r2_hidden(A_84, A_21) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_466])).
% 4.48/1.80  tff(c_894, plain, (![A_114, C_115, A_116]: (k1_funct_1(k5_relat_1(k6_relat_1(A_114), C_115), A_116)=k1_funct_1(C_115, k1_funct_1(k6_relat_1(A_114), A_116)) | ~r2_hidden(A_116, A_114) | ~v1_funct_1(C_115) | ~v1_relat_1(C_115))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_502])).
% 4.48/1.80  tff(c_990, plain, (![B_123, A_124, A_125]: (k1_funct_1(B_123, k1_funct_1(k6_relat_1(A_124), A_125))=k1_funct_1(k7_relat_1(B_123, A_124), A_125) | ~r2_hidden(A_125, A_124) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123) | ~v1_relat_1(B_123))), inference(superposition, [status(thm), theory('equality')], [c_30, c_894])).
% 4.48/1.80  tff(c_2051, plain, (![B_205, A_206, C_207]: (k1_funct_1(k7_relat_1(B_205, A_206), C_207)=k1_funct_1(B_205, C_207) | ~r2_hidden(C_207, A_206) | ~v1_funct_1(B_205) | ~v1_relat_1(B_205) | ~v1_relat_1(B_205) | ~r2_hidden(C_207, A_206))), inference(superposition, [status(thm), theory('equality')], [c_58, c_990])).
% 4.48/1.80  tff(c_46, plain, (k1_funct_1(k7_relat_1('#skF_6', '#skF_5'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.48/1.80  tff(c_2069, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2051, c_46])).
% 4.48/1.80  tff(c_2086, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_52, c_50, c_2069])).
% 4.48/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.80  
% 4.48/1.80  Inference rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Ref     : 0
% 4.48/1.80  #Sup     : 480
% 4.48/1.80  #Fact    : 0
% 4.48/1.80  #Define  : 0
% 4.48/1.80  #Split   : 0
% 4.48/1.80  #Chain   : 0
% 4.48/1.80  #Close   : 0
% 4.48/1.80  
% 4.48/1.80  Ordering : KBO
% 4.48/1.80  
% 4.48/1.80  Simplification rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Subsume      : 158
% 4.48/1.80  #Demod        : 232
% 4.48/1.80  #Tautology    : 65
% 4.48/1.80  #SimpNegUnit  : 0
% 4.48/1.80  #BackRed      : 1
% 4.48/1.80  
% 4.48/1.80  #Partial instantiations: 0
% 4.48/1.80  #Strategies tried      : 1
% 4.48/1.80  
% 4.48/1.80  Timing (in seconds)
% 4.48/1.80  ----------------------
% 4.48/1.80  Preprocessing        : 0.31
% 4.48/1.80  Parsing              : 0.16
% 4.48/1.80  CNF conversion       : 0.02
% 4.48/1.80  Main loop            : 0.71
% 4.48/1.80  Inferencing          : 0.24
% 4.48/1.80  Reduction            : 0.24
% 4.48/1.80  Demodulation         : 0.20
% 4.48/1.80  BG Simplification    : 0.03
% 4.48/1.80  Subsumption          : 0.15
% 4.48/1.80  Abstraction          : 0.05
% 4.48/1.80  MUC search           : 0.00
% 4.48/1.80  Cooper               : 0.00
% 4.48/1.80  Total                : 1.04
% 4.48/1.80  Index Insertion      : 0.00
% 4.48/1.80  Index Deletion       : 0.00
% 4.48/1.80  Index Matching       : 0.00
% 4.48/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------

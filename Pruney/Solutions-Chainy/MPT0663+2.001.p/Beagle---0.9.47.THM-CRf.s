%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:11 EST 2020

% Result     : Theorem 7.34s
% Output     : CNFRefutation 7.34s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 103 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 143 expanded)
%              Number of equality atoms :   23 (  57 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_34,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
       => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(c_8,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_97,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_128,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_97])).

tff(c_44,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_134,plain,(
    ! [B_56,A_55] : k3_xboole_0(B_56,A_55) = k3_xboole_0(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_44])).

tff(c_10,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_196,plain,(
    ! [A_63,B_64,C_65] : k2_enumset1(A_63,A_63,B_64,C_65) = k1_enumset1(A_63,B_64,C_65) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_16,plain,(
    ! [F_20,A_13,B_14,C_15] : r2_hidden(F_20,k2_enumset1(A_13,B_14,C_15,F_20)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_218,plain,(
    ! [C_67,A_68,B_69] : r2_hidden(C_67,k1_enumset1(A_68,B_69,C_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_16])).

tff(c_221,plain,(
    ! [B_9,A_8] : r2_hidden(B_9,k2_tarski(A_8,B_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_218])).

tff(c_46,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),A_23)
      | ~ r2_hidden(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_399,plain,(
    ! [A_128,B_129,A_130] :
      ( r1_tarski(k3_xboole_0(A_128,B_129),A_130)
      | ~ r2_hidden(A_130,k2_tarski(A_128,B_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_46])).

tff(c_419,plain,(
    ! [A_131,B_132] : r1_tarski(k3_xboole_0(A_131,B_132),B_132) ),
    inference(resolution,[status(thm)],[c_221,c_399])).

tff(c_463,plain,(
    ! [A_138,B_139] : r1_tarski(k3_xboole_0(A_138,B_139),A_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_419])).

tff(c_58,plain,(
    r2_hidden('#skF_4',k3_xboole_0(k1_relat_1('#skF_6'),'#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_154,plain,(
    r2_hidden('#skF_4',k3_xboole_0('#skF_5',k1_relat_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_58])).

tff(c_239,plain,(
    ! [C_74,B_75,A_76] :
      ( r2_hidden(C_74,B_75)
      | ~ r2_hidden(C_74,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_262,plain,(
    ! [B_75] :
      ( r2_hidden('#skF_4',B_75)
      | ~ r1_tarski(k3_xboole_0('#skF_5',k1_relat_1('#skF_6')),B_75) ) ),
    inference(resolution,[status(thm)],[c_154,c_239])).

tff(c_474,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_463,c_262])).

tff(c_62,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_430,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_419,c_262])).

tff(c_48,plain,(
    ! [A_25,C_27,B_26] :
      ( r2_hidden(A_25,k1_relat_1(k7_relat_1(C_27,B_26)))
      | ~ r2_hidden(A_25,k1_relat_1(C_27))
      | ~ r2_hidden(A_25,B_26)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_600,plain,(
    ! [C_156,B_157,A_158] :
      ( k1_funct_1(k7_relat_1(C_156,B_157),A_158) = k1_funct_1(C_156,A_158)
      | ~ r2_hidden(A_158,k1_relat_1(k7_relat_1(C_156,B_157)))
      | ~ v1_funct_1(C_156)
      | ~ v1_relat_1(C_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7280,plain,(
    ! [C_16134,B_16135,A_16136] :
      ( k1_funct_1(k7_relat_1(C_16134,B_16135),A_16136) = k1_funct_1(C_16134,A_16136)
      | ~ v1_funct_1(C_16134)
      | ~ r2_hidden(A_16136,k1_relat_1(C_16134))
      | ~ r2_hidden(A_16136,B_16135)
      | ~ v1_relat_1(C_16134) ) ),
    inference(resolution,[status(thm)],[c_48,c_600])).

tff(c_7332,plain,(
    ! [B_16135] :
      ( k1_funct_1(k7_relat_1('#skF_6',B_16135),'#skF_4') = k1_funct_1('#skF_6','#skF_4')
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden('#skF_4',B_16135)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_430,c_7280])).

tff(c_7356,plain,(
    ! [B_16253] :
      ( k1_funct_1(k7_relat_1('#skF_6',B_16253),'#skF_4') = k1_funct_1('#skF_6','#skF_4')
      | ~ r2_hidden('#skF_4',B_16253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_7332])).

tff(c_56,plain,(
    k1_funct_1(k7_relat_1('#skF_6','#skF_5'),'#skF_4') != k1_funct_1('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7362,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7356,c_56])).

tff(c_7378,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_474,c_7362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.34/2.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/2.56  
% 7.34/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/2.56  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 7.34/2.56  
% 7.34/2.56  %Foreground sorts:
% 7.34/2.56  
% 7.34/2.56  
% 7.34/2.56  %Background operators:
% 7.34/2.56  
% 7.34/2.56  
% 7.34/2.56  %Foreground operators:
% 7.34/2.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.34/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.34/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.34/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 7.34/2.56  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.34/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.34/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.34/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.34/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.34/2.56  tff('#skF_6', type, '#skF_6': $i).
% 7.34/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.34/2.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.34/2.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.34/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.34/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.34/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.34/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.34/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.34/2.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.34/2.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.34/2.56  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.34/2.56  
% 7.34/2.57  tff(f_34, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.34/2.57  tff(f_58, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.34/2.57  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 7.34/2.57  tff(f_38, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 7.34/2.57  tff(f_56, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 7.34/2.57  tff(f_62, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 7.34/2.57  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_funct_1)).
% 7.34/2.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.34/2.57  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 7.34/2.57  tff(f_78, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 7.34/2.57  tff(c_8, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.34/2.57  tff(c_97, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.34/2.57  tff(c_128, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_8, c_97])).
% 7.34/2.57  tff(c_44, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.34/2.57  tff(c_134, plain, (![B_56, A_55]: (k3_xboole_0(B_56, A_55)=k3_xboole_0(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_128, c_44])).
% 7.34/2.57  tff(c_10, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.34/2.57  tff(c_196, plain, (![A_63, B_64, C_65]: (k2_enumset1(A_63, A_63, B_64, C_65)=k1_enumset1(A_63, B_64, C_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.34/2.57  tff(c_16, plain, (![F_20, A_13, B_14, C_15]: (r2_hidden(F_20, k2_enumset1(A_13, B_14, C_15, F_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.34/2.57  tff(c_218, plain, (![C_67, A_68, B_69]: (r2_hidden(C_67, k1_enumset1(A_68, B_69, C_67)))), inference(superposition, [status(thm), theory('equality')], [c_196, c_16])).
% 7.34/2.57  tff(c_221, plain, (![B_9, A_8]: (r2_hidden(B_9, k2_tarski(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_218])).
% 7.34/2.57  tff(c_46, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), A_23) | ~r2_hidden(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.34/2.57  tff(c_399, plain, (![A_128, B_129, A_130]: (r1_tarski(k3_xboole_0(A_128, B_129), A_130) | ~r2_hidden(A_130, k2_tarski(A_128, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_46])).
% 7.34/2.57  tff(c_419, plain, (![A_131, B_132]: (r1_tarski(k3_xboole_0(A_131, B_132), B_132))), inference(resolution, [status(thm)], [c_221, c_399])).
% 7.34/2.57  tff(c_463, plain, (![A_138, B_139]: (r1_tarski(k3_xboole_0(A_138, B_139), A_138))), inference(superposition, [status(thm), theory('equality')], [c_134, c_419])).
% 7.34/2.57  tff(c_58, plain, (r2_hidden('#skF_4', k3_xboole_0(k1_relat_1('#skF_6'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.34/2.57  tff(c_154, plain, (r2_hidden('#skF_4', k3_xboole_0('#skF_5', k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_58])).
% 7.34/2.57  tff(c_239, plain, (![C_74, B_75, A_76]: (r2_hidden(C_74, B_75) | ~r2_hidden(C_74, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.34/2.57  tff(c_262, plain, (![B_75]: (r2_hidden('#skF_4', B_75) | ~r1_tarski(k3_xboole_0('#skF_5', k1_relat_1('#skF_6')), B_75))), inference(resolution, [status(thm)], [c_154, c_239])).
% 7.34/2.57  tff(c_474, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_463, c_262])).
% 7.34/2.57  tff(c_62, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.34/2.57  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.34/2.57  tff(c_430, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_419, c_262])).
% 7.34/2.57  tff(c_48, plain, (![A_25, C_27, B_26]: (r2_hidden(A_25, k1_relat_1(k7_relat_1(C_27, B_26))) | ~r2_hidden(A_25, k1_relat_1(C_27)) | ~r2_hidden(A_25, B_26) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.34/2.57  tff(c_600, plain, (![C_156, B_157, A_158]: (k1_funct_1(k7_relat_1(C_156, B_157), A_158)=k1_funct_1(C_156, A_158) | ~r2_hidden(A_158, k1_relat_1(k7_relat_1(C_156, B_157))) | ~v1_funct_1(C_156) | ~v1_relat_1(C_156))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.34/2.57  tff(c_7280, plain, (![C_16134, B_16135, A_16136]: (k1_funct_1(k7_relat_1(C_16134, B_16135), A_16136)=k1_funct_1(C_16134, A_16136) | ~v1_funct_1(C_16134) | ~r2_hidden(A_16136, k1_relat_1(C_16134)) | ~r2_hidden(A_16136, B_16135) | ~v1_relat_1(C_16134))), inference(resolution, [status(thm)], [c_48, c_600])).
% 7.34/2.57  tff(c_7332, plain, (![B_16135]: (k1_funct_1(k7_relat_1('#skF_6', B_16135), '#skF_4')=k1_funct_1('#skF_6', '#skF_4') | ~v1_funct_1('#skF_6') | ~r2_hidden('#skF_4', B_16135) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_430, c_7280])).
% 7.34/2.57  tff(c_7356, plain, (![B_16253]: (k1_funct_1(k7_relat_1('#skF_6', B_16253), '#skF_4')=k1_funct_1('#skF_6', '#skF_4') | ~r2_hidden('#skF_4', B_16253))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_7332])).
% 7.34/2.57  tff(c_56, plain, (k1_funct_1(k7_relat_1('#skF_6', '#skF_5'), '#skF_4')!=k1_funct_1('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.34/2.57  tff(c_7362, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7356, c_56])).
% 7.34/2.57  tff(c_7378, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_474, c_7362])).
% 7.34/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.34/2.57  
% 7.34/2.57  Inference rules
% 7.34/2.57  ----------------------
% 7.34/2.57  #Ref     : 0
% 7.34/2.57  #Sup     : 1240
% 7.34/2.57  #Fact    : 48
% 7.34/2.57  #Define  : 0
% 7.34/2.57  #Split   : 2
% 7.34/2.57  #Chain   : 0
% 7.34/2.57  #Close   : 0
% 7.34/2.57  
% 7.34/2.57  Ordering : KBO
% 7.34/2.57  
% 7.34/2.57  Simplification rules
% 7.34/2.57  ----------------------
% 7.34/2.57  #Subsume      : 380
% 7.34/2.57  #Demod        : 77
% 7.34/2.57  #Tautology    : 164
% 7.34/2.57  #SimpNegUnit  : 0
% 7.34/2.57  #BackRed      : 1
% 7.34/2.57  
% 7.34/2.57  #Partial instantiations: 7672
% 7.34/2.57  #Strategies tried      : 1
% 7.34/2.57  
% 7.34/2.57  Timing (in seconds)
% 7.34/2.57  ----------------------
% 7.34/2.57  Preprocessing        : 0.32
% 7.34/2.57  Parsing              : 0.16
% 7.34/2.57  CNF conversion       : 0.02
% 7.34/2.57  Main loop            : 1.49
% 7.34/2.57  Inferencing          : 0.73
% 7.34/2.57  Reduction            : 0.34
% 7.34/2.57  Demodulation         : 0.26
% 7.34/2.57  BG Simplification    : 0.07
% 7.34/2.57  Subsumption          : 0.28
% 7.34/2.57  Abstraction          : 0.11
% 7.34/2.57  MUC search           : 0.00
% 7.34/2.57  Cooper               : 0.00
% 7.34/2.57  Total                : 1.84
% 7.34/2.57  Index Insertion      : 0.00
% 7.34/2.57  Index Deletion       : 0.00
% 7.34/2.57  Index Matching       : 0.00
% 7.34/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

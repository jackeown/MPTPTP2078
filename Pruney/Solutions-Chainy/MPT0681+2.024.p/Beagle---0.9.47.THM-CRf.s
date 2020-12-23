%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:28 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 107 expanded)
%              Number of leaves         :   33 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :   71 ( 144 expanded)
%              Number of equality atoms :   28 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_10,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_276,plain,(
    ! [B_80,A_81] :
      ( k9_relat_1(B_80,A_81) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_301,plain,(
    ! [B_82] :
      ( k9_relat_1(B_82,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_82) ) ),
    inference(resolution,[status(thm)],[c_10,c_276])).

tff(c_305,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_301])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_63,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = A_52
      | ~ r1_xboole_0(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_75,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_109,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_109])).

tff(c_130,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_40,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_74,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_127,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_109])).

tff(c_174,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_127])).

tff(c_857,plain,(
    ! [C_135,A_136,B_137] :
      ( k3_xboole_0(k9_relat_1(C_135,A_136),k9_relat_1(C_135,B_137)) = k9_relat_1(C_135,k3_xboole_0(A_136,B_137))
      | ~ v2_funct_1(C_135)
      | ~ v1_funct_1(C_135)
      | ~ v1_relat_1(C_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_205,plain,(
    ! [A_72,B_73] :
      ( r2_hidden('#skF_1'(A_72,B_73),k3_xboole_0(A_72,B_73))
      | r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r1_xboole_0(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    ! [A_63] : k4_xboole_0(A_63,A_63) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_136,plain,(
    ! [A_63] : k4_xboole_0(A_63,k1_xboole_0) = k3_xboole_0(A_63,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_8])).

tff(c_152,plain,(
    ! [A_64] : k3_xboole_0(A_64,A_64) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_136])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [A_65,C_66] :
      ( ~ r1_xboole_0(A_65,A_65)
      | ~ r2_hidden(C_66,A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_4])).

tff(c_187,plain,(
    ! [C_66,B_11] :
      ( ~ r2_hidden(C_66,B_11)
      | k4_xboole_0(B_11,B_11) != B_11 ) ),
    inference(resolution,[status(thm)],[c_14,c_184])).

tff(c_192,plain,(
    ! [C_66,B_11] :
      ( ~ r2_hidden(C_66,B_11)
      | k1_xboole_0 != B_11 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_187])).

tff(c_227,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) != k1_xboole_0
      | r1_xboole_0(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_205,c_192])).

tff(c_36,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_239,plain,(
    k3_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_227,c_36])).

tff(c_880,plain,
    ( k9_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_239])).

tff(c_913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_305,c_174,c_880])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.39  
% 2.86/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.86/1.40  
% 2.86/1.40  %Foreground sorts:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Background operators:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Foreground operators:
% 2.86/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.86/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.86/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.40  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.86/1.40  
% 2.86/1.41  tff(f_88, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 2.86/1.41  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.86/1.41  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.86/1.41  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.86/1.41  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.86/1.41  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.86/1.41  tff(f_77, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 2.86/1.41  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.86/1.41  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.41  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.41  tff(c_38, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.41  tff(c_10, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.86/1.41  tff(c_276, plain, (![B_80, A_81]: (k9_relat_1(B_80, A_81)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.41  tff(c_301, plain, (![B_82]: (k9_relat_1(B_82, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_82))), inference(resolution, [status(thm)], [c_10, c_276])).
% 2.86/1.41  tff(c_305, plain, (k9_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_301])).
% 2.86/1.41  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.41  tff(c_63, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=A_52 | ~r1_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.41  tff(c_75, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(resolution, [status(thm)], [c_10, c_63])).
% 2.86/1.41  tff(c_109, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.41  tff(c_124, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_75, c_109])).
% 2.86/1.41  tff(c_130, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_124])).
% 2.86/1.41  tff(c_40, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.41  tff(c_74, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_40, c_63])).
% 2.86/1.41  tff(c_127, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_74, c_109])).
% 2.86/1.41  tff(c_174, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_130, c_127])).
% 2.86/1.41  tff(c_857, plain, (![C_135, A_136, B_137]: (k3_xboole_0(k9_relat_1(C_135, A_136), k9_relat_1(C_135, B_137))=k9_relat_1(C_135, k3_xboole_0(A_136, B_137)) | ~v2_funct_1(C_135) | ~v1_funct_1(C_135) | ~v1_relat_1(C_135))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.86/1.41  tff(c_205, plain, (![A_72, B_73]: (r2_hidden('#skF_1'(A_72, B_73), k3_xboole_0(A_72, B_73)) | r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.41  tff(c_14, plain, (![A_10, B_11]: (r1_xboole_0(A_10, B_11) | k4_xboole_0(A_10, B_11)!=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.41  tff(c_131, plain, (![A_63]: (k4_xboole_0(A_63, A_63)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_124])).
% 2.86/1.41  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.41  tff(c_136, plain, (![A_63]: (k4_xboole_0(A_63, k1_xboole_0)=k3_xboole_0(A_63, A_63))), inference(superposition, [status(thm), theory('equality')], [c_131, c_8])).
% 2.86/1.41  tff(c_152, plain, (![A_64]: (k3_xboole_0(A_64, A_64)=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_136])).
% 2.86/1.41  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.41  tff(c_184, plain, (![A_65, C_66]: (~r1_xboole_0(A_65, A_65) | ~r2_hidden(C_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_152, c_4])).
% 2.86/1.41  tff(c_187, plain, (![C_66, B_11]: (~r2_hidden(C_66, B_11) | k4_xboole_0(B_11, B_11)!=B_11)), inference(resolution, [status(thm)], [c_14, c_184])).
% 2.86/1.41  tff(c_192, plain, (![C_66, B_11]: (~r2_hidden(C_66, B_11) | k1_xboole_0!=B_11)), inference(demodulation, [status(thm), theory('equality')], [c_130, c_187])).
% 2.86/1.41  tff(c_227, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)!=k1_xboole_0 | r1_xboole_0(A_74, B_75))), inference(resolution, [status(thm)], [c_205, c_192])).
% 2.86/1.41  tff(c_36, plain, (~r1_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.41  tff(c_239, plain, (k3_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_227, c_36])).
% 2.86/1.41  tff(c_880, plain, (k9_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0 | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_857, c_239])).
% 2.86/1.41  tff(c_913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_305, c_174, c_880])).
% 2.86/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.41  
% 2.86/1.41  Inference rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Ref     : 0
% 2.86/1.41  #Sup     : 207
% 2.86/1.41  #Fact    : 0
% 2.86/1.41  #Define  : 0
% 2.86/1.41  #Split   : 0
% 2.86/1.41  #Chain   : 0
% 2.86/1.41  #Close   : 0
% 2.86/1.41  
% 2.86/1.41  Ordering : KBO
% 2.86/1.41  
% 2.86/1.41  Simplification rules
% 2.86/1.41  ----------------------
% 2.86/1.41  #Subsume      : 19
% 2.86/1.41  #Demod        : 95
% 2.86/1.41  #Tautology    : 109
% 2.86/1.41  #SimpNegUnit  : 4
% 2.86/1.41  #BackRed      : 0
% 2.86/1.41  
% 2.86/1.41  #Partial instantiations: 0
% 2.86/1.41  #Strategies tried      : 1
% 2.86/1.41  
% 2.86/1.41  Timing (in seconds)
% 2.86/1.41  ----------------------
% 2.86/1.41  Preprocessing        : 0.32
% 2.86/1.41  Parsing              : 0.17
% 2.86/1.41  CNF conversion       : 0.02
% 2.86/1.41  Main loop            : 0.33
% 2.86/1.41  Inferencing          : 0.14
% 2.86/1.41  Reduction            : 0.10
% 2.86/1.41  Demodulation         : 0.07
% 2.86/1.41  BG Simplification    : 0.02
% 2.86/1.41  Subsumption          : 0.05
% 2.86/1.41  Abstraction          : 0.02
% 2.86/1.41  MUC search           : 0.00
% 2.86/1.41  Cooper               : 0.00
% 2.86/1.41  Total                : 0.69
% 2.86/1.41  Index Insertion      : 0.00
% 2.86/1.41  Index Deletion       : 0.00
% 2.86/1.41  Index Matching       : 0.00
% 2.86/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 9.83s
% Output     : CNFRefutation 9.83s
% Verified   : 
% Statistics : Number of formulae       :   53 (  59 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   80 ( 108 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_53,plain,(
    ! [A_26,B_27] : r1_xboole_0(k4_xboole_0(A_26,B_27),B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_56,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_53])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_89,plain,(
    ! [A_34,B_35,C_36] :
      ( ~ r1_xboole_0(A_34,B_35)
      | ~ r2_hidden(C_36,k3_xboole_0(A_34,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_92,plain,(
    ! [A_13,C_36] :
      ( ~ r1_xboole_0(A_13,k1_xboole_0)
      | ~ r2_hidden(C_36,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_89])).

tff(c_94,plain,(
    ! [C_36] : ~ r2_hidden(C_36,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_92])).

tff(c_107,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_118,plain,(
    ! [A_6,B_7,A_40] :
      ( ~ r1_xboole_0(A_6,B_7)
      | r1_xboole_0(A_40,k3_xboole_0(A_6,B_7)) ) ),
    inference(resolution,[status(thm)],[c_107,c_10])).

tff(c_192,plain,(
    ! [B_58,A_59] :
      ( k9_relat_1(B_58,A_59) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_58),A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_201,plain,(
    ! [B_58,A_6,B_7] :
      ( k9_relat_1(B_58,k3_xboole_0(A_6,B_7)) = k1_xboole_0
      | ~ v1_relat_1(B_58)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_118,c_192])).

tff(c_290,plain,(
    ! [C_78,A_79,B_80] :
      ( k3_xboole_0(k9_relat_1(C_78,A_79),k9_relat_1(C_78,B_80)) = k9_relat_1(C_78,k3_xboole_0(A_79,B_80))
      | ~ v2_funct_1(C_78)
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),k3_xboole_0(A_6,B_7))
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3931,plain,(
    ! [C_188,A_189,B_190] :
      ( r2_hidden('#skF_2'(k9_relat_1(C_188,A_189),k9_relat_1(C_188,B_190)),k9_relat_1(C_188,k3_xboole_0(A_189,B_190)))
      | r1_xboole_0(k9_relat_1(C_188,A_189),k9_relat_1(C_188,B_190))
      | ~ v2_funct_1(C_188)
      | ~ v1_funct_1(C_188)
      | ~ v1_relat_1(C_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_8])).

tff(c_4161,plain,(
    ! [B_58,A_6,B_7] :
      ( r2_hidden('#skF_2'(k9_relat_1(B_58,A_6),k9_relat_1(B_58,B_7)),k1_xboole_0)
      | r1_xboole_0(k9_relat_1(B_58,A_6),k9_relat_1(B_58,B_7))
      | ~ v2_funct_1(B_58)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(B_58)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_3931])).

tff(c_30162,plain,(
    ! [B_566,A_567,B_568] :
      ( r1_xboole_0(k9_relat_1(B_566,A_567),k9_relat_1(B_566,B_568))
      | ~ v2_funct_1(B_566)
      | ~ v1_funct_1(B_566)
      | ~ v1_relat_1(B_566)
      | ~ v1_relat_1(B_566)
      | ~ r1_xboole_0(A_567,B_568) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4161])).

tff(c_28,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30173,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_30162,c_28])).

tff(c_30577,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_36,c_34,c_30,c_30173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.83/3.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.83/3.92  
% 9.83/3.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.83/3.92  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.83/3.92  
% 9.83/3.92  %Foreground sorts:
% 9.83/3.92  
% 9.83/3.92  
% 9.83/3.92  %Background operators:
% 9.83/3.92  
% 9.83/3.92  
% 9.83/3.92  %Foreground operators:
% 9.83/3.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.83/3.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.83/3.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.83/3.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.83/3.92  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.83/3.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.83/3.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.83/3.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.83/3.92  tff('#skF_5', type, '#skF_5': $i).
% 9.83/3.92  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.83/3.92  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.83/3.92  tff('#skF_3', type, '#skF_3': $i).
% 9.83/3.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.83/3.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.83/3.92  tff('#skF_4', type, '#skF_4': $i).
% 9.83/3.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.83/3.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.83/3.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.83/3.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.83/3.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.83/3.92  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.83/3.92  
% 9.83/3.93  tff(f_92, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_funct_1)).
% 9.83/3.93  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 9.83/3.93  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.83/3.93  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.83/3.93  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.83/3.93  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.83/3.93  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 9.83/3.93  tff(f_81, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 9.83/3.93  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.83/3.93  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.83/3.93  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.83/3.93  tff(c_30, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.83/3.93  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.83/3.93  tff(c_53, plain, (![A_26, B_27]: (r1_xboole_0(k4_xboole_0(A_26, B_27), B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.83/3.93  tff(c_56, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_53])).
% 9.83/3.93  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.83/3.93  tff(c_89, plain, (![A_34, B_35, C_36]: (~r1_xboole_0(A_34, B_35) | ~r2_hidden(C_36, k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.83/3.93  tff(c_92, plain, (![A_13, C_36]: (~r1_xboole_0(A_13, k1_xboole_0) | ~r2_hidden(C_36, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_89])).
% 9.83/3.93  tff(c_94, plain, (![C_36]: (~r2_hidden(C_36, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_92])).
% 9.83/3.93  tff(c_107, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), B_41) | r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.83/3.93  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.83/3.93  tff(c_118, plain, (![A_6, B_7, A_40]: (~r1_xboole_0(A_6, B_7) | r1_xboole_0(A_40, k3_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_107, c_10])).
% 9.83/3.93  tff(c_192, plain, (![B_58, A_59]: (k9_relat_1(B_58, A_59)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_58), A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_73])).
% 9.83/3.93  tff(c_201, plain, (![B_58, A_6, B_7]: (k9_relat_1(B_58, k3_xboole_0(A_6, B_7))=k1_xboole_0 | ~v1_relat_1(B_58) | ~r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_118, c_192])).
% 9.83/3.93  tff(c_290, plain, (![C_78, A_79, B_80]: (k3_xboole_0(k9_relat_1(C_78, A_79), k9_relat_1(C_78, B_80))=k9_relat_1(C_78, k3_xboole_0(A_79, B_80)) | ~v2_funct_1(C_78) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.83/3.93  tff(c_8, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), k3_xboole_0(A_6, B_7)) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.83/3.93  tff(c_3931, plain, (![C_188, A_189, B_190]: (r2_hidden('#skF_2'(k9_relat_1(C_188, A_189), k9_relat_1(C_188, B_190)), k9_relat_1(C_188, k3_xboole_0(A_189, B_190))) | r1_xboole_0(k9_relat_1(C_188, A_189), k9_relat_1(C_188, B_190)) | ~v2_funct_1(C_188) | ~v1_funct_1(C_188) | ~v1_relat_1(C_188))), inference(superposition, [status(thm), theory('equality')], [c_290, c_8])).
% 9.83/3.93  tff(c_4161, plain, (![B_58, A_6, B_7]: (r2_hidden('#skF_2'(k9_relat_1(B_58, A_6), k9_relat_1(B_58, B_7)), k1_xboole_0) | r1_xboole_0(k9_relat_1(B_58, A_6), k9_relat_1(B_58, B_7)) | ~v2_funct_1(B_58) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58) | ~v1_relat_1(B_58) | ~r1_xboole_0(A_6, B_7))), inference(superposition, [status(thm), theory('equality')], [c_201, c_3931])).
% 9.83/3.93  tff(c_30162, plain, (![B_566, A_567, B_568]: (r1_xboole_0(k9_relat_1(B_566, A_567), k9_relat_1(B_566, B_568)) | ~v2_funct_1(B_566) | ~v1_funct_1(B_566) | ~v1_relat_1(B_566) | ~v1_relat_1(B_566) | ~r1_xboole_0(A_567, B_568))), inference(negUnitSimplification, [status(thm)], [c_94, c_4161])).
% 9.83/3.93  tff(c_28, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.83/3.93  tff(c_30173, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_30162, c_28])).
% 9.83/3.93  tff(c_30577, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_36, c_34, c_30, c_30173])).
% 9.83/3.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.83/3.93  
% 9.83/3.93  Inference rules
% 9.83/3.93  ----------------------
% 9.83/3.93  #Ref     : 0
% 9.83/3.93  #Sup     : 7103
% 9.83/3.93  #Fact    : 0
% 9.83/3.93  #Define  : 0
% 9.83/3.93  #Split   : 0
% 9.83/3.93  #Chain   : 0
% 9.83/3.93  #Close   : 0
% 9.83/3.93  
% 9.83/3.93  Ordering : KBO
% 9.83/3.93  
% 9.83/3.93  Simplification rules
% 9.83/3.93  ----------------------
% 9.83/3.93  #Subsume      : 823
% 9.83/3.93  #Demod        : 10816
% 9.83/3.93  #Tautology    : 5333
% 9.83/3.93  #SimpNegUnit  : 94
% 9.83/3.93  #BackRed      : 1
% 9.83/3.93  
% 9.83/3.93  #Partial instantiations: 0
% 9.83/3.93  #Strategies tried      : 1
% 9.83/3.93  
% 9.83/3.93  Timing (in seconds)
% 9.83/3.93  ----------------------
% 9.83/3.93  Preprocessing        : 0.30
% 9.83/3.93  Parsing              : 0.17
% 9.83/3.94  CNF conversion       : 0.02
% 9.83/3.94  Main loop            : 2.86
% 9.83/3.94  Inferencing          : 0.79
% 9.83/3.94  Reduction            : 1.42
% 9.83/3.94  Demodulation         : 1.22
% 9.83/3.94  BG Simplification    : 0.07
% 9.83/3.94  Subsumption          : 0.46
% 9.83/3.94  Abstraction          : 0.13
% 9.83/3.94  MUC search           : 0.00
% 9.83/3.94  Cooper               : 0.00
% 9.83/3.94  Total                : 3.18
% 9.83/3.94  Index Insertion      : 0.00
% 9.83/3.94  Index Deletion       : 0.00
% 9.83/3.94  Index Matching       : 0.00
% 9.83/3.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------

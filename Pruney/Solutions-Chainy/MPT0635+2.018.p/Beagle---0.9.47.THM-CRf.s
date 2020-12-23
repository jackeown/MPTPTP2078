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
% DateTime   : Thu Dec  3 10:03:23 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 145 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k3_xboole_0(k1_relat_1(C),B))
         => k1_funct_1(C,A) = k1_funct_1(k5_relat_1(k6_relat_1(B),C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k1_funct_1(k6_relat_1(B),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_42,plain,(
    r2_hidden('#skF_3',k3_xboole_0(k1_relat_1('#skF_5'),'#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_96,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [D_42,A_43,B_44] :
      ( r2_hidden(D_42,A_43)
      | ~ r2_hidden(D_42,k3_xboole_0(A_43,B_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_6])).

tff(c_121,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_117])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [D_53,A_54,B_55] :
      ( ~ r2_hidden(D_53,k4_xboole_0(A_54,B_55))
      | ~ r2_hidden(D_53,k3_xboole_0(A_54,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4])).

tff(c_176,plain,(
    ! [D_56,A_57,B_58] :
      ( ~ r2_hidden(D_56,k3_xboole_0(A_57,B_58))
      | r2_hidden(D_56,B_58)
      | ~ r2_hidden(D_56,A_57) ) ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_179,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_176])).

tff(c_182,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_179])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( k1_funct_1(k6_relat_1(B_23),A_22) = A_22
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1088,plain,(
    ! [B_116,C_117,A_118] :
      ( k1_funct_1(k5_relat_1(B_116,C_117),A_118) = k1_funct_1(C_117,k1_funct_1(B_116,A_118))
      | ~ r2_hidden(A_118,k1_relat_1(B_116))
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117)
      | ~ v1_funct_1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1116,plain,(
    ! [A_16,C_117,A_118] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_16),C_117),A_118) = k1_funct_1(C_117,k1_funct_1(k6_relat_1(A_16),A_118))
      | ~ r2_hidden(A_118,A_16)
      | ~ v1_funct_1(C_117)
      | ~ v1_relat_1(C_117)
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1088])).

tff(c_2683,plain,(
    ! [A_153,C_154,A_155] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_153),C_154),A_155) = k1_funct_1(C_154,k1_funct_1(k6_relat_1(A_153),A_155))
      | ~ r2_hidden(A_155,A_153)
      | ~ v1_funct_1(C_154)
      | ~ v1_relat_1(C_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_1116])).

tff(c_40,plain,(
    k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'),'#skF_5'),'#skF_3') != k1_funct_1('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2689,plain,
    ( k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2683,c_40])).

tff(c_2695,plain,(
    k1_funct_1('#skF_5',k1_funct_1(k6_relat_1('#skF_4'),'#skF_3')) != k1_funct_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_182,c_2689])).

tff(c_2699,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_2695])).

tff(c_2703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_2699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:17:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.77  
% 4.43/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.77  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 4.43/1.77  
% 4.43/1.77  %Foreground sorts:
% 4.43/1.77  
% 4.43/1.77  
% 4.43/1.77  %Background operators:
% 4.43/1.77  
% 4.43/1.77  
% 4.43/1.77  %Foreground operators:
% 4.43/1.77  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.43/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.43/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.43/1.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.43/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.43/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.43/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.43/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.43/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.43/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.43/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.43/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.43/1.77  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.43/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.43/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.43/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.43/1.77  
% 4.43/1.78  tff(f_77, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k3_xboole_0(k1_relat_1(C), B)) => (k1_funct_1(C, A) = k1_funct_1(k5_relat_1(k6_relat_1(B), C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_1)).
% 4.43/1.78  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.43/1.78  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.43/1.78  tff(f_68, axiom, (![A, B]: (r2_hidden(A, B) => (k1_funct_1(k6_relat_1(B), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_1)).
% 4.43/1.78  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.43/1.78  tff(f_47, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.43/1.78  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 4.43/1.78  tff(c_42, plain, (r2_hidden('#skF_3', k3_xboole_0(k1_relat_1('#skF_5'), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.43/1.78  tff(c_96, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.43/1.78  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.78  tff(c_117, plain, (![D_42, A_43, B_44]: (r2_hidden(D_42, A_43) | ~r2_hidden(D_42, k3_xboole_0(A_43, B_44)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_6])).
% 4.43/1.78  tff(c_121, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_117])).
% 4.43/1.78  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.78  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.78  tff(c_165, plain, (![D_53, A_54, B_55]: (~r2_hidden(D_53, k4_xboole_0(A_54, B_55)) | ~r2_hidden(D_53, k3_xboole_0(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4])).
% 4.43/1.78  tff(c_176, plain, (![D_56, A_57, B_58]: (~r2_hidden(D_56, k3_xboole_0(A_57, B_58)) | r2_hidden(D_56, B_58) | ~r2_hidden(D_56, A_57))), inference(resolution, [status(thm)], [c_2, c_165])).
% 4.43/1.78  tff(c_179, plain, (r2_hidden('#skF_3', '#skF_4') | ~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_176])).
% 4.43/1.78  tff(c_182, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_179])).
% 4.43/1.78  tff(c_38, plain, (![B_23, A_22]: (k1_funct_1(k6_relat_1(B_23), A_22)=A_22 | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.43/1.78  tff(c_46, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.43/1.78  tff(c_44, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.43/1.78  tff(c_32, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.78  tff(c_34, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.78  tff(c_28, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.43/1.78  tff(c_1088, plain, (![B_116, C_117, A_118]: (k1_funct_1(k5_relat_1(B_116, C_117), A_118)=k1_funct_1(C_117, k1_funct_1(B_116, A_118)) | ~r2_hidden(A_118, k1_relat_1(B_116)) | ~v1_funct_1(C_117) | ~v1_relat_1(C_117) | ~v1_funct_1(B_116) | ~v1_relat_1(B_116))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.43/1.78  tff(c_1116, plain, (![A_16, C_117, A_118]: (k1_funct_1(k5_relat_1(k6_relat_1(A_16), C_117), A_118)=k1_funct_1(C_117, k1_funct_1(k6_relat_1(A_16), A_118)) | ~r2_hidden(A_118, A_16) | ~v1_funct_1(C_117) | ~v1_relat_1(C_117) | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1088])).
% 4.43/1.78  tff(c_2683, plain, (![A_153, C_154, A_155]: (k1_funct_1(k5_relat_1(k6_relat_1(A_153), C_154), A_155)=k1_funct_1(C_154, k1_funct_1(k6_relat_1(A_153), A_155)) | ~r2_hidden(A_155, A_153) | ~v1_funct_1(C_154) | ~v1_relat_1(C_154))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_1116])).
% 4.43/1.78  tff(c_40, plain, (k1_funct_1(k5_relat_1(k6_relat_1('#skF_4'), '#skF_5'), '#skF_3')!=k1_funct_1('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.43/1.78  tff(c_2689, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3') | ~r2_hidden('#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2683, c_40])).
% 4.43/1.78  tff(c_2695, plain, (k1_funct_1('#skF_5', k1_funct_1(k6_relat_1('#skF_4'), '#skF_3'))!=k1_funct_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_182, c_2689])).
% 4.43/1.78  tff(c_2699, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38, c_2695])).
% 4.43/1.78  tff(c_2703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_2699])).
% 4.43/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.78  
% 4.43/1.78  Inference rules
% 4.43/1.78  ----------------------
% 4.43/1.78  #Ref     : 0
% 4.43/1.78  #Sup     : 749
% 4.43/1.78  #Fact    : 0
% 4.43/1.78  #Define  : 0
% 4.43/1.78  #Split   : 0
% 4.43/1.78  #Chain   : 0
% 4.43/1.78  #Close   : 0
% 4.43/1.78  
% 4.43/1.78  Ordering : KBO
% 4.43/1.78  
% 4.43/1.78  Simplification rules
% 4.43/1.78  ----------------------
% 4.43/1.78  #Subsume      : 256
% 4.43/1.78  #Demod        : 68
% 4.43/1.78  #Tautology    : 55
% 4.43/1.78  #SimpNegUnit  : 9
% 4.43/1.78  #BackRed      : 0
% 4.43/1.78  
% 4.43/1.78  #Partial instantiations: 0
% 4.43/1.78  #Strategies tried      : 1
% 4.43/1.78  
% 4.43/1.78  Timing (in seconds)
% 4.43/1.78  ----------------------
% 4.51/1.78  Preprocessing        : 0.31
% 4.51/1.79  Parsing              : 0.16
% 4.51/1.79  CNF conversion       : 0.02
% 4.51/1.79  Main loop            : 0.72
% 4.51/1.79  Inferencing          : 0.25
% 4.51/1.79  Reduction            : 0.24
% 4.51/1.79  Demodulation         : 0.20
% 4.51/1.79  BG Simplification    : 0.03
% 4.51/1.79  Subsumption          : 0.15
% 4.51/1.79  Abstraction          : 0.05
% 4.51/1.79  MUC search           : 0.00
% 4.51/1.79  Cooper               : 0.00
% 4.51/1.79  Total                : 1.05
% 4.51/1.79  Index Insertion      : 0.00
% 4.51/1.79  Index Deletion       : 0.00
% 4.51/1.79  Index Matching       : 0.00
% 4.51/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------

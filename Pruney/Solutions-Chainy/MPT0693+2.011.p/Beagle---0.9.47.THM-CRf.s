%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:52 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  65 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k10_relat_1(B_20,k3_xboole_0(k2_relat_1(B_20),A_19)) = k10_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_415,plain,(
    ! [B_59,A_60] :
      ( k9_relat_1(B_59,k10_relat_1(B_59,A_60)) = A_60
      | ~ r1_tarski(A_60,k2_relat_1(B_59))
      | ~ v1_funct_1(B_59)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_634,plain,(
    ! [B_71,B_72] :
      ( k9_relat_1(B_71,k10_relat_1(B_71,k4_xboole_0(k2_relat_1(B_71),B_72))) = k4_xboole_0(k2_relat_1(B_71),B_72)
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(resolution,[status(thm)],[c_4,c_415])).

tff(c_664,plain,(
    ! [B_71,B_6] :
      ( k9_relat_1(B_71,k10_relat_1(B_71,k3_xboole_0(k2_relat_1(B_71),B_6))) = k4_xboole_0(k2_relat_1(B_71),k4_xboole_0(k2_relat_1(B_71),B_6))
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_634])).

tff(c_746,plain,(
    ! [B_75,B_76] :
      ( k9_relat_1(B_75,k10_relat_1(B_75,k3_xboole_0(k2_relat_1(B_75),B_76))) = k3_xboole_0(k2_relat_1(B_75),B_76)
      | ~ v1_funct_1(B_75)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_664])).

tff(c_778,plain,(
    ! [B_77,A_78] :
      ( k9_relat_1(B_77,k10_relat_1(B_77,A_78)) = k3_xboole_0(k2_relat_1(B_77),A_78)
      | ~ v1_funct_1(B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(B_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_746])).

tff(c_16,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22])).

tff(c_117,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_115])).

tff(c_792,plain,
    ( k3_xboole_0(k2_relat_1('#skF_2'),'#skF_1') != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_117])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_24,c_2,c_792])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.37  
% 2.60/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.38  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.60/1.38  
% 2.60/1.38  %Foreground sorts:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Background operators:
% 2.60/1.38  
% 2.60/1.38  
% 2.60/1.38  %Foreground operators:
% 2.60/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.60/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.60/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.60/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.60/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.60/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.60/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.60/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.60/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.60/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.60/1.38  
% 2.60/1.39  tff(f_62, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 2.60/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.60/1.39  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 2.60/1.39  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.60/1.39  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.60/1.39  tff(f_55, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.60/1.39  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.60/1.39  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.60/1.39  tff(c_24, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.60/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.39  tff(c_18, plain, (![B_20, A_19]: (k10_relat_1(B_20, k3_xboole_0(k2_relat_1(B_20), A_19))=k10_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.39  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.39  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.39  tff(c_415, plain, (![B_59, A_60]: (k9_relat_1(B_59, k10_relat_1(B_59, A_60))=A_60 | ~r1_tarski(A_60, k2_relat_1(B_59)) | ~v1_funct_1(B_59) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.60/1.39  tff(c_634, plain, (![B_71, B_72]: (k9_relat_1(B_71, k10_relat_1(B_71, k4_xboole_0(k2_relat_1(B_71), B_72)))=k4_xboole_0(k2_relat_1(B_71), B_72) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(resolution, [status(thm)], [c_4, c_415])).
% 2.60/1.39  tff(c_664, plain, (![B_71, B_6]: (k9_relat_1(B_71, k10_relat_1(B_71, k3_xboole_0(k2_relat_1(B_71), B_6)))=k4_xboole_0(k2_relat_1(B_71), k4_xboole_0(k2_relat_1(B_71), B_6)) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71))), inference(superposition, [status(thm), theory('equality')], [c_6, c_634])).
% 2.60/1.39  tff(c_746, plain, (![B_75, B_76]: (k9_relat_1(B_75, k10_relat_1(B_75, k3_xboole_0(k2_relat_1(B_75), B_76)))=k3_xboole_0(k2_relat_1(B_75), B_76) | ~v1_funct_1(B_75) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_664])).
% 2.60/1.39  tff(c_778, plain, (![B_77, A_78]: (k9_relat_1(B_77, k10_relat_1(B_77, A_78))=k3_xboole_0(k2_relat_1(B_77), A_78) | ~v1_funct_1(B_77) | ~v1_relat_1(B_77) | ~v1_relat_1(B_77))), inference(superposition, [status(thm), theory('equality')], [c_18, c_746])).
% 2.60/1.39  tff(c_16, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.60/1.39  tff(c_22, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.60/1.39  tff(c_115, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_22])).
% 2.60/1.39  tff(c_117, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_115])).
% 2.60/1.39  tff(c_792, plain, (k3_xboole_0(k2_relat_1('#skF_2'), '#skF_1')!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_778, c_117])).
% 2.60/1.39  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_24, c_2, c_792])).
% 2.60/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.39  
% 2.60/1.39  Inference rules
% 2.60/1.39  ----------------------
% 2.60/1.39  #Ref     : 0
% 2.60/1.39  #Sup     : 191
% 2.60/1.39  #Fact    : 0
% 2.60/1.39  #Define  : 0
% 2.60/1.39  #Split   : 0
% 2.60/1.39  #Chain   : 0
% 2.60/1.39  #Close   : 0
% 2.60/1.39  
% 2.86/1.39  Ordering : KBO
% 2.86/1.39  
% 2.86/1.39  Simplification rules
% 2.86/1.39  ----------------------
% 2.86/1.39  #Subsume      : 6
% 2.86/1.39  #Demod        : 101
% 2.86/1.39  #Tautology    : 110
% 2.86/1.39  #SimpNegUnit  : 0
% 2.86/1.39  #BackRed      : 0
% 2.86/1.39  
% 2.86/1.39  #Partial instantiations: 0
% 2.86/1.39  #Strategies tried      : 1
% 2.86/1.39  
% 2.86/1.39  Timing (in seconds)
% 2.86/1.39  ----------------------
% 2.86/1.39  Preprocessing        : 0.29
% 2.86/1.39  Parsing              : 0.16
% 2.86/1.39  CNF conversion       : 0.02
% 2.86/1.39  Main loop            : 0.34
% 2.86/1.39  Inferencing          : 0.11
% 2.86/1.39  Reduction            : 0.15
% 2.86/1.39  Demodulation         : 0.13
% 2.86/1.39  BG Simplification    : 0.02
% 2.86/1.39  Subsumption          : 0.04
% 2.86/1.39  Abstraction          : 0.02
% 2.86/1.39  MUC search           : 0.00
% 2.86/1.39  Cooper               : 0.00
% 2.86/1.39  Total                : 0.66
% 2.86/1.39  Index Insertion      : 0.00
% 2.86/1.39  Index Deletion       : 0.00
% 2.86/1.39  Index Matching       : 0.00
% 2.86/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

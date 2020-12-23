%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:04 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 102 expanded)
%              Number of leaves         :   26 (  48 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 234 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_73,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_73])).

tff(c_972,plain,(
    ! [C_86,A_87,B_88] :
      ( k3_xboole_0(k9_relat_1(C_86,A_87),k9_relat_1(C_86,B_88)) = k9_relat_1(C_86,k3_xboole_0(A_87,B_88))
      | ~ v2_funct_1(C_86)
      | ~ v1_funct_1(C_86)
      | ~ v1_relat_1(C_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1021,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_972])).

tff(c_1038,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_1021])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k10_relat_1(B_22,k9_relat_1(B_22,A_21)),A_21)
      | ~ v2_funct_1(B_22)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1202,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1038,c_24])).

tff(c_1213,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_28,c_1202])).

tff(c_103,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    ! [A_31,B_32] : r1_tarski(k3_xboole_0(A_31,B_32),A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_282,plain,(
    ! [A_44,C_45,B_46] :
      ( r1_tarski(A_44,C_45)
      | ~ r1_tarski(B_46,C_45)
      | ~ r1_tarski(A_44,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_296,plain,(
    ! [A_44,A_31,B_32] :
      ( r1_tarski(A_44,A_31)
      | ~ r1_tarski(A_44,k3_xboole_0(A_31,B_32)) ) ),
    inference(resolution,[status(thm)],[c_112,c_282])).

tff(c_6174,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1213,c_296])).

tff(c_558,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(A_66,k10_relat_1(B_67,k9_relat_1(B_67,A_66)))
      | ~ r1_tarski(A_66,k1_relat_1(B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_567,plain,(
    ! [B_67,A_66] :
      ( k10_relat_1(B_67,k9_relat_1(B_67,A_66)) = A_66
      | ~ r1_tarski(k10_relat_1(B_67,k9_relat_1(B_67,A_66)),A_66)
      | ~ r1_tarski(A_66,k1_relat_1(B_67))
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_558,c_4])).

tff(c_6196,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6174,c_567])).

tff(c_6210,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30,c_6196])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_121,plain,(
    ! [A_33,B_34] : r1_tarski(k3_xboole_0(A_33,B_34),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_133,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_121])).

tff(c_295,plain,(
    ! [A_44,A_1,B_2] :
      ( r1_tarski(A_44,A_1)
      | ~ r1_tarski(A_44,k3_xboole_0(B_2,A_1)) ) ),
    inference(resolution,[status(thm)],[c_133,c_282])).

tff(c_6173,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1213,c_295])).

tff(c_6219,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6210,c_6173])).

tff(c_6223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_6219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:59:01 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/2.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.18  
% 5.24/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.18  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.24/2.18  
% 5.24/2.18  %Foreground sorts:
% 5.24/2.18  
% 5.24/2.18  
% 5.24/2.18  %Background operators:
% 5.24/2.18  
% 5.24/2.18  
% 5.24/2.18  %Foreground operators:
% 5.24/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.24/2.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.24/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/2.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.24/2.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.24/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.24/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.24/2.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.24/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.24/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.24/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/2.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.24/2.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.24/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/2.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.24/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.24/2.18  
% 5.24/2.19  tff(f_84, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.24/2.19  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.24/2.19  tff(f_57, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_1)).
% 5.24/2.19  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 5.24/2.19  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.24/2.19  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.24/2.19  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.24/2.19  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.24/2.19  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.24/2.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.24/2.19  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.24/2.19  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.24/2.19  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.24/2.19  tff(c_34, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.24/2.19  tff(c_28, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.24/2.19  tff(c_32, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.24/2.19  tff(c_73, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.24/2.19  tff(c_86, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_73])).
% 5.24/2.19  tff(c_972, plain, (![C_86, A_87, B_88]: (k3_xboole_0(k9_relat_1(C_86, A_87), k9_relat_1(C_86, B_88))=k9_relat_1(C_86, k3_xboole_0(A_87, B_88)) | ~v2_funct_1(C_86) | ~v1_funct_1(C_86) | ~v1_relat_1(C_86))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.24/2.19  tff(c_1021, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_86, c_972])).
% 5.24/2.19  tff(c_1038, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_1021])).
% 5.24/2.19  tff(c_24, plain, (![B_22, A_21]: (r1_tarski(k10_relat_1(B_22, k9_relat_1(B_22, A_21)), A_21) | ~v2_funct_1(B_22) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.24/2.19  tff(c_1202, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1038, c_24])).
% 5.24/2.19  tff(c_1213, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_28, c_1202])).
% 5.24/2.19  tff(c_103, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.24/2.19  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.24/2.19  tff(c_112, plain, (![A_31, B_32]: (r1_tarski(k3_xboole_0(A_31, B_32), A_31))), inference(superposition, [status(thm), theory('equality')], [c_103, c_16])).
% 5.24/2.19  tff(c_282, plain, (![A_44, C_45, B_46]: (r1_tarski(A_44, C_45) | ~r1_tarski(B_46, C_45) | ~r1_tarski(A_44, B_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.24/2.19  tff(c_296, plain, (![A_44, A_31, B_32]: (r1_tarski(A_44, A_31) | ~r1_tarski(A_44, k3_xboole_0(A_31, B_32)))), inference(resolution, [status(thm)], [c_112, c_282])).
% 5.24/2.19  tff(c_6174, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_1')), inference(resolution, [status(thm)], [c_1213, c_296])).
% 5.24/2.19  tff(c_558, plain, (![A_66, B_67]: (r1_tarski(A_66, k10_relat_1(B_67, k9_relat_1(B_67, A_66))) | ~r1_tarski(A_66, k1_relat_1(B_67)) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.24/2.19  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.24/2.19  tff(c_567, plain, (![B_67, A_66]: (k10_relat_1(B_67, k9_relat_1(B_67, A_66))=A_66 | ~r1_tarski(k10_relat_1(B_67, k9_relat_1(B_67, A_66)), A_66) | ~r1_tarski(A_66, k1_relat_1(B_67)) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_558, c_4])).
% 5.24/2.19  tff(c_6196, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6174, c_567])).
% 5.24/2.19  tff(c_6210, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30, c_6196])).
% 5.24/2.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.24/2.19  tff(c_121, plain, (![A_33, B_34]: (r1_tarski(k3_xboole_0(A_33, B_34), A_33))), inference(superposition, [status(thm), theory('equality')], [c_103, c_16])).
% 5.24/2.19  tff(c_133, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_121])).
% 5.24/2.19  tff(c_295, plain, (![A_44, A_1, B_2]: (r1_tarski(A_44, A_1) | ~r1_tarski(A_44, k3_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_133, c_282])).
% 5.24/2.19  tff(c_6173, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), '#skF_2')), inference(resolution, [status(thm)], [c_1213, c_295])).
% 5.24/2.19  tff(c_6219, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6210, c_6173])).
% 5.24/2.19  tff(c_6223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_6219])).
% 5.24/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.19  
% 5.24/2.19  Inference rules
% 5.24/2.19  ----------------------
% 5.24/2.19  #Ref     : 0
% 5.24/2.19  #Sup     : 1516
% 5.24/2.19  #Fact    : 0
% 5.24/2.19  #Define  : 0
% 5.24/2.19  #Split   : 4
% 5.24/2.19  #Chain   : 0
% 5.24/2.19  #Close   : 0
% 5.24/2.19  
% 5.24/2.19  Ordering : KBO
% 5.24/2.19  
% 5.24/2.19  Simplification rules
% 5.24/2.19  ----------------------
% 5.24/2.19  #Subsume      : 170
% 5.24/2.19  #Demod        : 1105
% 5.24/2.19  #Tautology    : 819
% 5.24/2.19  #SimpNegUnit  : 1
% 5.24/2.19  #BackRed      : 3
% 5.24/2.19  
% 5.24/2.19  #Partial instantiations: 0
% 5.24/2.19  #Strategies tried      : 1
% 5.24/2.19  
% 5.24/2.19  Timing (in seconds)
% 5.24/2.19  ----------------------
% 5.24/2.20  Preprocessing        : 0.29
% 5.24/2.20  Parsing              : 0.16
% 5.24/2.20  CNF conversion       : 0.02
% 5.24/2.20  Main loop            : 1.12
% 5.24/2.20  Inferencing          : 0.32
% 5.24/2.20  Reduction            : 0.50
% 5.24/2.20  Demodulation         : 0.41
% 5.24/2.20  BG Simplification    : 0.03
% 5.24/2.20  Subsumption          : 0.20
% 5.24/2.20  Abstraction          : 0.06
% 5.24/2.20  MUC search           : 0.00
% 5.24/2.20  Cooper               : 0.00
% 5.24/2.20  Total                : 1.44
% 5.24/2.20  Index Insertion      : 0.00
% 5.24/2.20  Index Deletion       : 0.00
% 5.24/2.20  Index Matching       : 0.00
% 5.24/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:09 EST 2020

% Result     : Theorem 10.40s
% Output     : CNFRefutation 10.40s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 105 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 186 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_553,plain,(
    ! [B_55,A_56] :
      ( k9_relat_1(B_55,k10_relat_1(B_55,A_56)) = A_56
      | ~ r1_tarski(A_56,k2_relat_1(B_55))
      | ~ v1_funct_1(B_55)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_565,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_553])).

tff(c_579,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_565])).

tff(c_26,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_159,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_175,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_159])).

tff(c_852,plain,(
    ! [C_70,A_71,B_72] :
      ( k3_xboole_0(k10_relat_1(C_70,A_71),k10_relat_1(C_70,B_72)) = k10_relat_1(C_70,k3_xboole_0(A_71,B_72))
      | ~ v1_funct_1(C_70)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_901,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_852])).

tff(c_918,plain,(
    k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_901])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_246,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(k2_xboole_0(A_36,B_38),C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_264,plain,(
    ! [A_39,B_40] : r1_tarski(A_39,k2_xboole_0(A_39,B_40)) ),
    inference(resolution,[status(thm)],[c_8,c_246])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_332,plain,(
    ! [A_43,B_44,B_45] : r1_tarski(A_43,k2_xboole_0(k2_xboole_0(A_43,B_44),B_45)) ),
    inference(resolution,[status(thm)],[c_264,c_10])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_360,plain,(
    ! [A_43,B_44,B_45] : k3_xboole_0(A_43,k2_xboole_0(k2_xboole_0(A_43,B_44),B_45)) = A_43 ),
    inference(resolution,[status(thm)],[c_332,c_16])).

tff(c_83,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_1785,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(k3_xboole_0(A_90,B_91),C_92)
      | ~ r1_tarski(A_90,C_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_246])).

tff(c_20187,plain,(
    ! [A_346,B_347,C_348] :
      ( k3_xboole_0(k3_xboole_0(A_346,B_347),C_348) = k3_xboole_0(A_346,B_347)
      | ~ r1_tarski(A_346,C_348) ) ),
    inference(resolution,[status(thm)],[c_1785,c_16])).

tff(c_102,plain,(
    k2_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_83])).

tff(c_34,plain,(
    ! [B_22,A_23] : k3_xboole_0(B_22,A_23) = k3_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [B_22,A_23] : r1_tarski(k3_xboole_0(B_22,A_23),A_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_100,plain,(
    ! [B_22,A_23] : k2_xboole_0(k3_xboole_0(B_22,A_23),A_23) = A_23 ),
    inference(resolution,[status(thm)],[c_49,c_83])).

tff(c_443,plain,(
    ! [B_50,A_51,B_52] : r1_tarski(k3_xboole_0(B_50,A_51),k2_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_332])).

tff(c_472,plain,(
    ! [B_50] : r1_tarski(k3_xboole_0(B_50,'#skF_1'),k2_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_443])).

tff(c_21016,plain,(
    ! [A_350,B_351] :
      ( r1_tarski(k3_xboole_0(A_350,B_351),k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_350,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20187,c_472])).

tff(c_21171,plain,(
    ! [A_352] :
      ( r1_tarski(A_352,k2_relat_1('#skF_3'))
      | ~ r1_tarski(A_352,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_21016])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( k9_relat_1(B_18,k10_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k2_relat_1(B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_21204,plain,(
    ! [A_352] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_352)) = A_352
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_352,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_21171,c_20])).

tff(c_23993,plain,(
    ! [A_369] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_369)) = A_369
      | ~ r1_tarski(A_369,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_21204])).

tff(c_24045,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_23993])).

tff(c_24079,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_579,c_24045])).

tff(c_24594,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_24079,c_49])).

tff(c_24669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_24594])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.40/4.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/4.24  
% 10.40/4.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/4.24  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 10.40/4.24  
% 10.40/4.24  %Foreground sorts:
% 10.40/4.24  
% 10.40/4.24  
% 10.40/4.24  %Background operators:
% 10.40/4.24  
% 10.40/4.24  
% 10.40/4.24  %Foreground operators:
% 10.40/4.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.40/4.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.40/4.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.40/4.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.40/4.24  tff('#skF_2', type, '#skF_2': $i).
% 10.40/4.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 10.40/4.24  tff('#skF_3', type, '#skF_3': $i).
% 10.40/4.24  tff('#skF_1', type, '#skF_1': $i).
% 10.40/4.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.40/4.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.40/4.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.40/4.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.40/4.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.40/4.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.40/4.24  
% 10.40/4.25  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 10.40/4.25  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.40/4.25  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 10.40/4.25  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.40/4.25  tff(f_53, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 10.40/4.25  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.40/4.25  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.40/4.25  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.40/4.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.40/4.25  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.40/4.25  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.40/4.25  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.40/4.25  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.40/4.25  tff(c_24, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.40/4.25  tff(c_553, plain, (![B_55, A_56]: (k9_relat_1(B_55, k10_relat_1(B_55, A_56))=A_56 | ~r1_tarski(A_56, k2_relat_1(B_55)) | ~v1_funct_1(B_55) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.40/4.25  tff(c_565, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_553])).
% 10.40/4.25  tff(c_579, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_565])).
% 10.40/4.25  tff(c_26, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.40/4.25  tff(c_159, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.40/4.25  tff(c_175, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_159])).
% 10.40/4.25  tff(c_852, plain, (![C_70, A_71, B_72]: (k3_xboole_0(k10_relat_1(C_70, A_71), k10_relat_1(C_70, B_72))=k10_relat_1(C_70, k3_xboole_0(A_71, B_72)) | ~v1_funct_1(C_70) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.40/4.25  tff(c_901, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_852])).
% 10.40/4.25  tff(c_918, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_901])).
% 10.40/4.25  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.40/4.25  tff(c_246, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(k2_xboole_0(A_36, B_38), C_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.40/4.25  tff(c_264, plain, (![A_39, B_40]: (r1_tarski(A_39, k2_xboole_0(A_39, B_40)))), inference(resolution, [status(thm)], [c_8, c_246])).
% 10.40/4.25  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.40/4.25  tff(c_332, plain, (![A_43, B_44, B_45]: (r1_tarski(A_43, k2_xboole_0(k2_xboole_0(A_43, B_44), B_45)))), inference(resolution, [status(thm)], [c_264, c_10])).
% 10.40/4.25  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.40/4.25  tff(c_360, plain, (![A_43, B_44, B_45]: (k3_xboole_0(A_43, k2_xboole_0(k2_xboole_0(A_43, B_44), B_45))=A_43)), inference(resolution, [status(thm)], [c_332, c_16])).
% 10.40/4.25  tff(c_83, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.40/4.25  tff(c_101, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_14, c_83])).
% 10.40/4.25  tff(c_1785, plain, (![A_90, B_91, C_92]: (r1_tarski(k3_xboole_0(A_90, B_91), C_92) | ~r1_tarski(A_90, C_92))), inference(superposition, [status(thm), theory('equality')], [c_101, c_246])).
% 10.40/4.25  tff(c_20187, plain, (![A_346, B_347, C_348]: (k3_xboole_0(k3_xboole_0(A_346, B_347), C_348)=k3_xboole_0(A_346, B_347) | ~r1_tarski(A_346, C_348))), inference(resolution, [status(thm)], [c_1785, c_16])).
% 10.40/4.25  tff(c_102, plain, (k2_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_83])).
% 10.40/4.25  tff(c_34, plain, (![B_22, A_23]: (k3_xboole_0(B_22, A_23)=k3_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.40/4.25  tff(c_49, plain, (![B_22, A_23]: (r1_tarski(k3_xboole_0(B_22, A_23), A_23))), inference(superposition, [status(thm), theory('equality')], [c_34, c_14])).
% 10.40/4.25  tff(c_100, plain, (![B_22, A_23]: (k2_xboole_0(k3_xboole_0(B_22, A_23), A_23)=A_23)), inference(resolution, [status(thm)], [c_49, c_83])).
% 10.40/4.25  tff(c_443, plain, (![B_50, A_51, B_52]: (r1_tarski(k3_xboole_0(B_50, A_51), k2_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_332])).
% 10.40/4.25  tff(c_472, plain, (![B_50]: (r1_tarski(k3_xboole_0(B_50, '#skF_1'), k2_relat_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_102, c_443])).
% 10.40/4.25  tff(c_21016, plain, (![A_350, B_351]: (r1_tarski(k3_xboole_0(A_350, B_351), k2_relat_1('#skF_3')) | ~r1_tarski(A_350, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20187, c_472])).
% 10.40/4.25  tff(c_21171, plain, (![A_352]: (r1_tarski(A_352, k2_relat_1('#skF_3')) | ~r1_tarski(A_352, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_360, c_21016])).
% 10.40/4.25  tff(c_20, plain, (![B_18, A_17]: (k9_relat_1(B_18, k10_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k2_relat_1(B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.40/4.25  tff(c_21204, plain, (![A_352]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_352))=A_352 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_352, '#skF_1'))), inference(resolution, [status(thm)], [c_21171, c_20])).
% 10.40/4.25  tff(c_23993, plain, (![A_369]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_369))=A_369 | ~r1_tarski(A_369, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_21204])).
% 10.40/4.25  tff(c_24045, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_918, c_23993])).
% 10.40/4.25  tff(c_24079, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_579, c_24045])).
% 10.40/4.25  tff(c_24594, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_24079, c_49])).
% 10.40/4.25  tff(c_24669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_24594])).
% 10.40/4.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.40/4.25  
% 10.40/4.25  Inference rules
% 10.40/4.25  ----------------------
% 10.40/4.25  #Ref     : 0
% 10.40/4.25  #Sup     : 6126
% 10.40/4.25  #Fact    : 0
% 10.40/4.25  #Define  : 0
% 10.40/4.25  #Split   : 3
% 10.40/4.25  #Chain   : 0
% 10.40/4.25  #Close   : 0
% 10.40/4.25  
% 10.40/4.25  Ordering : KBO
% 10.40/4.25  
% 10.40/4.25  Simplification rules
% 10.40/4.25  ----------------------
% 10.40/4.25  #Subsume      : 566
% 10.40/4.25  #Demod        : 5485
% 10.40/4.25  #Tautology    : 3561
% 10.40/4.25  #SimpNegUnit  : 1
% 10.40/4.25  #BackRed      : 2
% 10.40/4.25  
% 10.40/4.25  #Partial instantiations: 0
% 10.40/4.25  #Strategies tried      : 1
% 10.40/4.25  
% 10.40/4.26  Timing (in seconds)
% 10.40/4.26  ----------------------
% 10.40/4.26  Preprocessing        : 0.27
% 10.40/4.26  Parsing              : 0.15
% 10.40/4.26  CNF conversion       : 0.02
% 10.40/4.26  Main loop            : 3.16
% 10.40/4.26  Inferencing          : 0.62
% 10.40/4.26  Reduction            : 1.73
% 10.40/4.26  Demodulation         : 1.52
% 10.40/4.26  BG Simplification    : 0.07
% 10.40/4.26  Subsumption          : 0.58
% 10.40/4.26  Abstraction          : 0.12
% 10.40/4.26  MUC search           : 0.00
% 10.40/4.26  Cooper               : 0.00
% 10.40/4.26  Total                : 3.46
% 10.40/4.26  Index Insertion      : 0.00
% 10.40/4.26  Index Deletion       : 0.00
% 10.40/4.26  Index Matching       : 0.00
% 10.40/4.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

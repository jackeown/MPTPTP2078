%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 5.44s
% Output     : CNFRefutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 164 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_349,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k10_relat_1(B_45,k9_relat_1(B_45,A_46)),A_46)
      | ~ v2_funct_1(B_45)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_356,plain,(
    ! [B_45,A_46] :
      ( k2_xboole_0(k10_relat_1(B_45,k9_relat_1(B_45,A_46)),A_46) = A_46
      | ~ v2_funct_1(B_45)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_349,c_10])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k10_relat_1(B_14,k9_relat_1(B_14,A_13)),A_13)
      | ~ v2_funct_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_598,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,k10_relat_1(B_62,k9_relat_1(B_62,A_61)))
      | ~ r1_tarski(A_61,k1_relat_1(B_62))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2821,plain,(
    ! [B_163,A_164] :
      ( k10_relat_1(B_163,k9_relat_1(B_163,A_164)) = A_164
      | ~ r1_tarski(k10_relat_1(B_163,k9_relat_1(B_163,A_164)),A_164)
      | ~ r1_tarski(A_164,k1_relat_1(B_163))
      | ~ v1_relat_1(B_163) ) ),
    inference(resolution,[status(thm)],[c_598,c_2])).

tff(c_3511,plain,(
    ! [B_200,A_201] :
      ( k10_relat_1(B_200,k9_relat_1(B_200,A_201)) = A_201
      | ~ r1_tarski(A_201,k1_relat_1(B_200))
      | ~ v2_funct_1(B_200)
      | ~ v1_funct_1(B_200)
      | ~ v1_relat_1(B_200) ) ),
    inference(resolution,[status(thm)],[c_16,c_2821])).

tff(c_3519,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_3511])).

tff(c_3527,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_20,c_3519])).

tff(c_104,plain,(
    ! [C_26,A_27,B_28] :
      ( r1_tarski(k10_relat_1(C_26,A_27),k10_relat_1(C_26,B_28))
      | ~ r1_tarski(A_27,B_28)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1260,plain,(
    ! [C_93,A_94,B_95] :
      ( k2_xboole_0(k10_relat_1(C_93,A_94),k10_relat_1(C_93,B_95)) = k10_relat_1(C_93,B_95)
      | ~ r1_tarski(A_94,B_95)
      | ~ v1_relat_1(C_93) ) ),
    inference(resolution,[status(thm)],[c_104,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_71,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(k2_xboole_0(A_21,B_23),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_3,B_4,B_25] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_25)) ),
    inference(resolution,[status(thm)],[c_83,c_8])).

tff(c_1291,plain,(
    ! [C_93,A_94,B_95,B_25] :
      ( r1_tarski(k10_relat_1(C_93,A_94),k2_xboole_0(k10_relat_1(C_93,B_95),B_25))
      | ~ r1_tarski(A_94,B_95)
      | ~ v1_relat_1(C_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_99])).

tff(c_3576,plain,(
    ! [B_95,B_25] :
      ( r1_tarski('#skF_1',k2_xboole_0(k10_relat_1('#skF_3',B_95),B_25))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_95)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3527,c_1291])).

tff(c_4462,plain,(
    ! [B_226,B_227] :
      ( r1_tarski('#skF_1',k2_xboole_0(k10_relat_1('#skF_3',B_226),B_227))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3576])).

tff(c_4494,plain,(
    ! [A_46] :
      ( r1_tarski('#skF_1',A_46)
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',A_46))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_4462])).

tff(c_4521,plain,(
    ! [A_228] :
      ( r1_tarski('#skF_1',A_228)
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3',A_228)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_20,c_4494])).

tff(c_4524,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_4521])).

tff(c_4532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_4524])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.44/2.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.10  
% 5.44/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.10  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 5.44/2.10  
% 5.44/2.10  %Foreground sorts:
% 5.44/2.10  
% 5.44/2.10  
% 5.44/2.10  %Background operators:
% 5.44/2.10  
% 5.44/2.10  
% 5.44/2.10  %Foreground operators:
% 5.44/2.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.44/2.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.44/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.44/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.44/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.44/2.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.44/2.10  tff('#skF_3', type, '#skF_3': $i).
% 5.44/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.44/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.44/2.10  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.44/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.44/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.44/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.44/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.44/2.10  
% 5.63/2.12  tff(f_72, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 5.63/2.12  tff(f_59, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 5.63/2.12  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.63/2.12  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.63/2.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.63/2.12  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 5.63/2.12  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.63/2.12  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.63/2.12  tff(c_24, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.63/2.12  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.63/2.12  tff(c_26, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.63/2.12  tff(c_20, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.63/2.12  tff(c_349, plain, (![B_45, A_46]: (r1_tarski(k10_relat_1(B_45, k9_relat_1(B_45, A_46)), A_46) | ~v2_funct_1(B_45) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.63/2.12  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.63/2.12  tff(c_356, plain, (![B_45, A_46]: (k2_xboole_0(k10_relat_1(B_45, k9_relat_1(B_45, A_46)), A_46)=A_46 | ~v2_funct_1(B_45) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_349, c_10])).
% 5.63/2.12  tff(c_22, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.63/2.12  tff(c_16, plain, (![B_14, A_13]: (r1_tarski(k10_relat_1(B_14, k9_relat_1(B_14, A_13)), A_13) | ~v2_funct_1(B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.63/2.12  tff(c_598, plain, (![A_61, B_62]: (r1_tarski(A_61, k10_relat_1(B_62, k9_relat_1(B_62, A_61))) | ~r1_tarski(A_61, k1_relat_1(B_62)) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.63/2.12  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.63/2.12  tff(c_2821, plain, (![B_163, A_164]: (k10_relat_1(B_163, k9_relat_1(B_163, A_164))=A_164 | ~r1_tarski(k10_relat_1(B_163, k9_relat_1(B_163, A_164)), A_164) | ~r1_tarski(A_164, k1_relat_1(B_163)) | ~v1_relat_1(B_163))), inference(resolution, [status(thm)], [c_598, c_2])).
% 5.63/2.12  tff(c_3511, plain, (![B_200, A_201]: (k10_relat_1(B_200, k9_relat_1(B_200, A_201))=A_201 | ~r1_tarski(A_201, k1_relat_1(B_200)) | ~v2_funct_1(B_200) | ~v1_funct_1(B_200) | ~v1_relat_1(B_200))), inference(resolution, [status(thm)], [c_16, c_2821])).
% 5.63/2.12  tff(c_3519, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_3511])).
% 5.63/2.12  tff(c_3527, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_20, c_3519])).
% 5.63/2.12  tff(c_104, plain, (![C_26, A_27, B_28]: (r1_tarski(k10_relat_1(C_26, A_27), k10_relat_1(C_26, B_28)) | ~r1_tarski(A_27, B_28) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.63/2.12  tff(c_1260, plain, (![C_93, A_94, B_95]: (k2_xboole_0(k10_relat_1(C_93, A_94), k10_relat_1(C_93, B_95))=k10_relat_1(C_93, B_95) | ~r1_tarski(A_94, B_95) | ~v1_relat_1(C_93))), inference(resolution, [status(thm)], [c_104, c_10])).
% 5.63/2.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.63/2.12  tff(c_71, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(k2_xboole_0(A_21, B_23), C_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.63/2.12  tff(c_83, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(resolution, [status(thm)], [c_6, c_71])).
% 5.63/2.12  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.63/2.12  tff(c_99, plain, (![A_3, B_4, B_25]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_25)))), inference(resolution, [status(thm)], [c_83, c_8])).
% 5.63/2.12  tff(c_1291, plain, (![C_93, A_94, B_95, B_25]: (r1_tarski(k10_relat_1(C_93, A_94), k2_xboole_0(k10_relat_1(C_93, B_95), B_25)) | ~r1_tarski(A_94, B_95) | ~v1_relat_1(C_93))), inference(superposition, [status(thm), theory('equality')], [c_1260, c_99])).
% 5.63/2.12  tff(c_3576, plain, (![B_95, B_25]: (r1_tarski('#skF_1', k2_xboole_0(k10_relat_1('#skF_3', B_95), B_25)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_95) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3527, c_1291])).
% 5.63/2.12  tff(c_4462, plain, (![B_226, B_227]: (r1_tarski('#skF_1', k2_xboole_0(k10_relat_1('#skF_3', B_226), B_227)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_226))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3576])).
% 5.63/2.12  tff(c_4494, plain, (![A_46]: (r1_tarski('#skF_1', A_46) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', A_46)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_356, c_4462])).
% 5.63/2.12  tff(c_4521, plain, (![A_228]: (r1_tarski('#skF_1', A_228) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', A_228)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_20, c_4494])).
% 5.63/2.12  tff(c_4524, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_4521])).
% 5.63/2.12  tff(c_4532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_4524])).
% 5.63/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.63/2.12  
% 5.63/2.12  Inference rules
% 5.63/2.12  ----------------------
% 5.63/2.12  #Ref     : 0
% 5.63/2.12  #Sup     : 1079
% 5.63/2.12  #Fact    : 0
% 5.63/2.12  #Define  : 0
% 5.63/2.12  #Split   : 4
% 5.63/2.12  #Chain   : 0
% 5.63/2.12  #Close   : 0
% 5.63/2.12  
% 5.63/2.12  Ordering : KBO
% 5.63/2.12  
% 5.63/2.12  Simplification rules
% 5.63/2.12  ----------------------
% 5.63/2.12  #Subsume      : 144
% 5.63/2.12  #Demod        : 388
% 5.63/2.12  #Tautology    : 279
% 5.63/2.12  #SimpNegUnit  : 1
% 5.63/2.12  #BackRed      : 0
% 5.63/2.12  
% 5.63/2.12  #Partial instantiations: 0
% 5.63/2.12  #Strategies tried      : 1
% 5.63/2.12  
% 5.63/2.12  Timing (in seconds)
% 5.63/2.12  ----------------------
% 5.63/2.12  Preprocessing        : 0.28
% 5.63/2.12  Parsing              : 0.16
% 5.63/2.12  CNF conversion       : 0.02
% 5.63/2.12  Main loop            : 1.01
% 5.63/2.12  Inferencing          : 0.32
% 5.63/2.12  Reduction            : 0.34
% 5.63/2.12  Demodulation         : 0.26
% 5.63/2.12  BG Simplification    : 0.04
% 5.63/2.12  Subsumption          : 0.24
% 5.63/2.12  Abstraction          : 0.05
% 5.63/2.12  MUC search           : 0.00
% 5.63/2.12  Cooper               : 0.00
% 5.63/2.12  Total                : 1.31
% 5.63/2.12  Index Insertion      : 0.00
% 5.63/2.12  Index Deletion       : 0.00
% 5.63/2.12  Index Matching       : 0.00
% 5.63/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

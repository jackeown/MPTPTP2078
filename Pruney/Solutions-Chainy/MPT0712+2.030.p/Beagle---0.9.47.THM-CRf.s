%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:35 EST 2020

% Result     : Theorem 4.36s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   32 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 114 expanded)
%              Number of equality atoms :   28 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_88,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => r1_tarski(k2_relat_1(k7_relat_1(B,k1_tarski(A))),k1_tarski(k1_funct_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k1_relat_1(C)) )
       => k9_relat_1(C,k2_tarski(A,B)) = k2_tarski(k1_funct_1(C,A),k1_funct_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_24,plain,(
    ! [B_14] : r1_tarski(k1_xboole_0,k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_117,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(A_43,B_44) = k1_xboole_0
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_125,plain,(
    ! [B_14] : k4_xboole_0(k1_xboole_0,k1_tarski(B_14)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_117])).

tff(c_40,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_48,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    ! [B_14] : r1_tarski(k1_tarski(B_14),k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),B_10)
      | r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_363,plain,(
    ! [A_76,B_77] :
      ( k7_relat_1(A_76,B_77) = k1_xboole_0
      | ~ r1_xboole_0(B_77,k1_relat_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_381,plain,(
    ! [A_76,A_9] :
      ( k7_relat_1(A_76,k1_tarski(A_9)) = k1_xboole_0
      | ~ v1_relat_1(A_76)
      | r2_hidden(A_9,k1_relat_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_16,c_363])).

tff(c_14,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_384,plain,(
    ! [C_78,A_79,B_80] :
      ( k2_tarski(k1_funct_1(C_78,A_79),k1_funct_1(C_78,B_80)) = k9_relat_1(C_78,k2_tarski(A_79,B_80))
      | ~ r2_hidden(B_80,k1_relat_1(C_78))
      | ~ r2_hidden(A_79,k1_relat_1(C_78))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_401,plain,(
    ! [C_78,A_79] :
      ( k9_relat_1(C_78,k2_tarski(A_79,A_79)) = k1_tarski(k1_funct_1(C_78,A_79))
      | ~ r2_hidden(A_79,k1_relat_1(C_78))
      | ~ r2_hidden(A_79,k1_relat_1(C_78))
      | ~ v1_funct_1(C_78)
      | ~ v1_relat_1(C_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_384])).

tff(c_1186,plain,(
    ! [C_129,A_130] :
      ( k9_relat_1(C_129,k1_tarski(A_130)) = k1_tarski(k1_funct_1(C_129,A_130))
      | ~ r2_hidden(A_130,k1_relat_1(C_129))
      | ~ r2_hidden(A_130,k1_relat_1(C_129))
      | ~ v1_funct_1(C_129)
      | ~ v1_relat_1(C_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_401])).

tff(c_2663,plain,(
    ! [A_185,A_186] :
      ( k9_relat_1(A_185,k1_tarski(A_186)) = k1_tarski(k1_funct_1(A_185,A_186))
      | ~ r2_hidden(A_186,k1_relat_1(A_185))
      | ~ v1_funct_1(A_185)
      | k7_relat_1(A_185,k1_tarski(A_186)) = k1_xboole_0
      | ~ v1_relat_1(A_185) ) ),
    inference(resolution,[status(thm)],[c_381,c_1186])).

tff(c_2773,plain,(
    ! [A_189,A_190] :
      ( k9_relat_1(A_189,k1_tarski(A_190)) = k1_tarski(k1_funct_1(A_189,A_190))
      | ~ v1_funct_1(A_189)
      | k7_relat_1(A_189,k1_tarski(A_190)) = k1_xboole_0
      | ~ v1_relat_1(A_189) ) ),
    inference(resolution,[status(thm)],[c_381,c_2663])).

tff(c_302,plain,(
    ! [B_69,A_70] :
      ( k2_relat_1(k7_relat_1(B_69,A_70)) = k9_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_46,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_311,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_46])).

tff(c_319,plain,(
    ~ r1_tarski(k9_relat_1('#skF_2',k1_tarski('#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_311])).

tff(c_2820,plain,
    ( ~ r1_tarski(k1_tarski(k1_funct_1('#skF_2','#skF_1')),k1_tarski(k1_funct_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_319])).

tff(c_2841,plain,(
    k7_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_22,c_2820])).

tff(c_202,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(A_53,B_54)
      | k4_xboole_0(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_210,plain,(
    k4_xboole_0(k2_relat_1(k7_relat_1('#skF_2',k1_tarski('#skF_1'))),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_202,c_46])).

tff(c_2845,plain,(
    k4_xboole_0(k2_relat_1(k1_xboole_0),k1_tarski(k1_funct_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2841,c_210])).

tff(c_2849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_40,c_2845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:09:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.36/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.74  
% 4.36/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k3_tarski > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.36/1.75  
% 4.36/1.75  %Foreground sorts:
% 4.36/1.75  
% 4.36/1.75  
% 4.36/1.75  %Background operators:
% 4.36/1.75  
% 4.36/1.75  
% 4.36/1.75  %Foreground operators:
% 4.36/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.36/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.36/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.36/1.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.36/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.36/1.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.36/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.36/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.36/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.36/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.36/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.36/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.36/1.75  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.36/1.75  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 4.36/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.36/1.75  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.36/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.36/1.75  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.36/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.36/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.36/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.36/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.36/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.36/1.75  
% 4.36/1.76  tff(f_60, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 4.36/1.76  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.36/1.76  tff(f_88, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.36/1.76  tff(f_105, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k2_relat_1(k7_relat_1(B, k1_tarski(A))), k1_tarski(k1_funct_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_funct_1)).
% 4.36/1.76  tff(f_52, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 4.36/1.76  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t187_relat_1)).
% 4.36/1.76  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.36/1.76  tff(f_98, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k1_relat_1(C))) => (k9_relat_1(C, k2_tarski(A, B)) = k2_tarski(k1_funct_1(C, A), k1_funct_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_funct_1)).
% 4.36/1.76  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.36/1.76  tff(c_24, plain, (![B_14]: (r1_tarski(k1_xboole_0, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.36/1.76  tff(c_117, plain, (![A_43, B_44]: (k4_xboole_0(A_43, B_44)=k1_xboole_0 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.76  tff(c_125, plain, (![B_14]: (k4_xboole_0(k1_xboole_0, k1_tarski(B_14))=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_117])).
% 4.36/1.76  tff(c_40, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.36/1.76  tff(c_50, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.36/1.76  tff(c_48, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.36/1.76  tff(c_22, plain, (![B_14]: (r1_tarski(k1_tarski(B_14), k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.36/1.76  tff(c_16, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), B_10) | r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.36/1.76  tff(c_363, plain, (![A_76, B_77]: (k7_relat_1(A_76, B_77)=k1_xboole_0 | ~r1_xboole_0(B_77, k1_relat_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.36/1.76  tff(c_381, plain, (![A_76, A_9]: (k7_relat_1(A_76, k1_tarski(A_9))=k1_xboole_0 | ~v1_relat_1(A_76) | r2_hidden(A_9, k1_relat_1(A_76)))), inference(resolution, [status(thm)], [c_16, c_363])).
% 4.36/1.76  tff(c_14, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.36/1.76  tff(c_384, plain, (![C_78, A_79, B_80]: (k2_tarski(k1_funct_1(C_78, A_79), k1_funct_1(C_78, B_80))=k9_relat_1(C_78, k2_tarski(A_79, B_80)) | ~r2_hidden(B_80, k1_relat_1(C_78)) | ~r2_hidden(A_79, k1_relat_1(C_78)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.36/1.76  tff(c_401, plain, (![C_78, A_79]: (k9_relat_1(C_78, k2_tarski(A_79, A_79))=k1_tarski(k1_funct_1(C_78, A_79)) | ~r2_hidden(A_79, k1_relat_1(C_78)) | ~r2_hidden(A_79, k1_relat_1(C_78)) | ~v1_funct_1(C_78) | ~v1_relat_1(C_78))), inference(superposition, [status(thm), theory('equality')], [c_14, c_384])).
% 4.36/1.76  tff(c_1186, plain, (![C_129, A_130]: (k9_relat_1(C_129, k1_tarski(A_130))=k1_tarski(k1_funct_1(C_129, A_130)) | ~r2_hidden(A_130, k1_relat_1(C_129)) | ~r2_hidden(A_130, k1_relat_1(C_129)) | ~v1_funct_1(C_129) | ~v1_relat_1(C_129))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_401])).
% 4.36/1.76  tff(c_2663, plain, (![A_185, A_186]: (k9_relat_1(A_185, k1_tarski(A_186))=k1_tarski(k1_funct_1(A_185, A_186)) | ~r2_hidden(A_186, k1_relat_1(A_185)) | ~v1_funct_1(A_185) | k7_relat_1(A_185, k1_tarski(A_186))=k1_xboole_0 | ~v1_relat_1(A_185))), inference(resolution, [status(thm)], [c_381, c_1186])).
% 4.36/1.76  tff(c_2773, plain, (![A_189, A_190]: (k9_relat_1(A_189, k1_tarski(A_190))=k1_tarski(k1_funct_1(A_189, A_190)) | ~v1_funct_1(A_189) | k7_relat_1(A_189, k1_tarski(A_190))=k1_xboole_0 | ~v1_relat_1(A_189))), inference(resolution, [status(thm)], [c_381, c_2663])).
% 4.36/1.76  tff(c_302, plain, (![B_69, A_70]: (k2_relat_1(k7_relat_1(B_69, A_70))=k9_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.36/1.76  tff(c_46, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.36/1.76  tff(c_311, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_302, c_46])).
% 4.36/1.76  tff(c_319, plain, (~r1_tarski(k9_relat_1('#skF_2', k1_tarski('#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_311])).
% 4.36/1.76  tff(c_2820, plain, (~r1_tarski(k1_tarski(k1_funct_1('#skF_2', '#skF_1')), k1_tarski(k1_funct_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_2') | k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2773, c_319])).
% 4.36/1.76  tff(c_2841, plain, (k7_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_22, c_2820])).
% 4.36/1.76  tff(c_202, plain, (![A_53, B_54]: (r1_tarski(A_53, B_54) | k4_xboole_0(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.76  tff(c_210, plain, (k4_xboole_0(k2_relat_1(k7_relat_1('#skF_2', k1_tarski('#skF_1'))), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_202, c_46])).
% 4.36/1.76  tff(c_2845, plain, (k4_xboole_0(k2_relat_1(k1_xboole_0), k1_tarski(k1_funct_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2841, c_210])).
% 4.36/1.76  tff(c_2849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_40, c_2845])).
% 4.36/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.76  
% 4.36/1.76  Inference rules
% 4.36/1.76  ----------------------
% 4.36/1.76  #Ref     : 0
% 4.36/1.76  #Sup     : 621
% 4.36/1.76  #Fact    : 0
% 4.36/1.76  #Define  : 0
% 4.36/1.76  #Split   : 2
% 4.36/1.76  #Chain   : 0
% 4.36/1.76  #Close   : 0
% 4.36/1.76  
% 4.36/1.76  Ordering : KBO
% 4.36/1.76  
% 4.36/1.76  Simplification rules
% 4.36/1.76  ----------------------
% 4.36/1.76  #Subsume      : 125
% 4.36/1.76  #Demod        : 942
% 4.36/1.76  #Tautology    : 341
% 4.36/1.76  #SimpNegUnit  : 2
% 4.36/1.76  #BackRed      : 3
% 4.36/1.76  
% 4.36/1.76  #Partial instantiations: 0
% 4.36/1.76  #Strategies tried      : 1
% 4.36/1.76  
% 4.36/1.76  Timing (in seconds)
% 4.36/1.76  ----------------------
% 4.36/1.76  Preprocessing        : 0.31
% 4.36/1.76  Parsing              : 0.16
% 4.36/1.76  CNF conversion       : 0.02
% 4.36/1.76  Main loop            : 0.70
% 4.36/1.76  Inferencing          : 0.23
% 4.36/1.76  Reduction            : 0.28
% 4.36/1.76  Demodulation         : 0.22
% 4.36/1.76  BG Simplification    : 0.03
% 4.36/1.76  Subsumption          : 0.12
% 4.36/1.76  Abstraction          : 0.03
% 4.36/1.76  MUC search           : 0.00
% 4.36/1.76  Cooper               : 0.00
% 4.36/1.76  Total                : 1.04
% 4.36/1.76  Index Insertion      : 0.00
% 4.36/1.76  Index Deletion       : 0.00
% 4.36/1.76  Index Matching       : 0.00
% 4.36/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------

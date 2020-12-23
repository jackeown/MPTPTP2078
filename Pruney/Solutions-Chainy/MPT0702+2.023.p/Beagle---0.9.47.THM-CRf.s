%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:05 EST 2020

% Result     : Theorem 4.18s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 121 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  129 ( 362 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_51,plain,(
    ! [A_21,C_22,B_23] :
      ( r1_tarski(A_21,C_22)
      | ~ r1_tarski(B_23,C_22)
      | ~ r1_tarski(A_21,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    ! [A_21] :
      ( r1_tarski(A_21,k9_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_21,k9_relat_1('#skF_3','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(k2_funct_1(B_15),A_14) = k10_relat_1(B_15,A_14)
      | ~ v2_funct_1(B_15)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k10_relat_1(B_13,k9_relat_1(B_13,A_12)),A_12)
      | ~ v2_funct_1(B_13)
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_126,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,k10_relat_1(B_33,k9_relat_1(B_33,A_32)))
      | ~ r1_tarski(A_32,k1_relat_1(B_33))
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_988,plain,(
    ! [B_102,A_103] :
      ( k10_relat_1(B_102,k9_relat_1(B_102,A_103)) = A_103
      | ~ r1_tarski(k10_relat_1(B_102,k9_relat_1(B_102,A_103)),A_103)
      | ~ r1_tarski(A_103,k1_relat_1(B_102))
      | ~ v1_relat_1(B_102) ) ),
    inference(resolution,[status(thm)],[c_126,c_2])).

tff(c_1011,plain,(
    ! [B_104,A_105] :
      ( k10_relat_1(B_104,k9_relat_1(B_104,A_105)) = A_105
      | ~ r1_tarski(A_105,k1_relat_1(B_104))
      | ~ v2_funct_1(B_104)
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(resolution,[status(thm)],[c_18,c_988])).

tff(c_1018,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1011])).

tff(c_1028,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1018])).

tff(c_151,plain,(
    ! [B_36,A_37] :
      ( k9_relat_1(k2_funct_1(B_36),A_37) = k10_relat_1(B_36,A_37)
      | ~ v2_funct_1(B_36)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [C_8,A_6,B_7] :
      ( r1_tarski(k9_relat_1(C_8,A_6),k9_relat_1(C_8,B_7))
      | ~ r1_tarski(A_6,B_7)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1563,plain,(
    ! [B_133,A_134,B_135] :
      ( r1_tarski(k10_relat_1(B_133,A_134),k9_relat_1(k2_funct_1(B_133),B_135))
      | ~ r1_tarski(A_134,B_135)
      | ~ v1_relat_1(k2_funct_1(B_133))
      | ~ v2_funct_1(B_133)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_10])).

tff(c_1606,plain,(
    ! [B_135] :
      ( r1_tarski('#skF_1',k9_relat_1(k2_funct_1('#skF_3'),B_135))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_135)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_1563])).

tff(c_1629,plain,(
    ! [B_135] :
      ( r1_tarski('#skF_1',k9_relat_1(k2_funct_1('#skF_3'),B_135))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_135)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1606])).

tff(c_1655,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1629])).

tff(c_1658,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_1655])).

tff(c_1662,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1658])).

tff(c_1733,plain,(
    ! [B_139] :
      ( r1_tarski('#skF_1',k9_relat_1(k2_funct_1('#skF_3'),B_139))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_139) ) ),
    inference(splitRight,[status(thm)],[c_1629])).

tff(c_1767,plain,(
    ! [A_14] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_3',A_14))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_14)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1733])).

tff(c_1790,plain,(
    ! [A_140] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_3',A_140))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1767])).

tff(c_1828,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')))
    | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_1790])).

tff(c_1861,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1828])).

tff(c_141,plain,(
    ! [B_34,A_35] :
      ( r1_tarski(k10_relat_1(B_34,k9_relat_1(B_34,A_35)),A_35)
      | ~ v2_funct_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_149,plain,(
    ! [A_3,A_35,B_34] :
      ( r1_tarski(A_3,A_35)
      | ~ r1_tarski(A_3,k10_relat_1(B_34,k9_relat_1(B_34,A_35)))
      | ~ v2_funct_1(B_34)
      | ~ v1_funct_1(B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_141,c_8])).

tff(c_1884,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1861,c_149])).

tff(c_1908,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_1884])).

tff(c_1910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_1908])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.18/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.81  
% 4.43/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.81  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.43/1.81  
% 4.43/1.81  %Foreground sorts:
% 4.43/1.81  
% 4.43/1.81  
% 4.43/1.81  %Background operators:
% 4.43/1.81  
% 4.43/1.81  
% 4.43/1.81  %Foreground operators:
% 4.43/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.43/1.81  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.43/1.81  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.43/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.43/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.43/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.43/1.81  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.43/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.43/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.43/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.43/1.81  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.43/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.43/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.43/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.43/1.81  
% 4.43/1.82  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 4.43/1.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.43/1.82  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.43/1.82  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 4.43/1.82  tff(f_51, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.43/1.82  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 4.43/1.82  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.43/1.82  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 4.43/1.82  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.43/1.82  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.43/1.82  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.43/1.82  tff(c_24, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.43/1.82  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.43/1.82  tff(c_28, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.43/1.82  tff(c_51, plain, (![A_21, C_22, B_23]: (r1_tarski(A_21, C_22) | ~r1_tarski(B_23, C_22) | ~r1_tarski(A_21, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.43/1.82  tff(c_58, plain, (![A_21]: (r1_tarski(A_21, k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_21, k9_relat_1('#skF_3', '#skF_1')))), inference(resolution, [status(thm)], [c_28, c_51])).
% 4.43/1.82  tff(c_20, plain, (![B_15, A_14]: (k9_relat_1(k2_funct_1(B_15), A_14)=k10_relat_1(B_15, A_14) | ~v2_funct_1(B_15) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.43/1.82  tff(c_14, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.82  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.43/1.82  tff(c_18, plain, (![B_13, A_12]: (r1_tarski(k10_relat_1(B_13, k9_relat_1(B_13, A_12)), A_12) | ~v2_funct_1(B_13) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.43/1.82  tff(c_126, plain, (![A_32, B_33]: (r1_tarski(A_32, k10_relat_1(B_33, k9_relat_1(B_33, A_32))) | ~r1_tarski(A_32, k1_relat_1(B_33)) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.43/1.82  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.43/1.82  tff(c_988, plain, (![B_102, A_103]: (k10_relat_1(B_102, k9_relat_1(B_102, A_103))=A_103 | ~r1_tarski(k10_relat_1(B_102, k9_relat_1(B_102, A_103)), A_103) | ~r1_tarski(A_103, k1_relat_1(B_102)) | ~v1_relat_1(B_102))), inference(resolution, [status(thm)], [c_126, c_2])).
% 4.43/1.82  tff(c_1011, plain, (![B_104, A_105]: (k10_relat_1(B_104, k9_relat_1(B_104, A_105))=A_105 | ~r1_tarski(A_105, k1_relat_1(B_104)) | ~v2_funct_1(B_104) | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(resolution, [status(thm)], [c_18, c_988])).
% 4.43/1.82  tff(c_1018, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1011])).
% 4.43/1.82  tff(c_1028, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1018])).
% 4.43/1.82  tff(c_151, plain, (![B_36, A_37]: (k9_relat_1(k2_funct_1(B_36), A_37)=k10_relat_1(B_36, A_37) | ~v2_funct_1(B_36) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.43/1.82  tff(c_10, plain, (![C_8, A_6, B_7]: (r1_tarski(k9_relat_1(C_8, A_6), k9_relat_1(C_8, B_7)) | ~r1_tarski(A_6, B_7) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.43/1.82  tff(c_1563, plain, (![B_133, A_134, B_135]: (r1_tarski(k10_relat_1(B_133, A_134), k9_relat_1(k2_funct_1(B_133), B_135)) | ~r1_tarski(A_134, B_135) | ~v1_relat_1(k2_funct_1(B_133)) | ~v2_funct_1(B_133) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(superposition, [status(thm), theory('equality')], [c_151, c_10])).
% 4.43/1.82  tff(c_1606, plain, (![B_135]: (r1_tarski('#skF_1', k9_relat_1(k2_funct_1('#skF_3'), B_135)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_135) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1028, c_1563])).
% 4.43/1.82  tff(c_1629, plain, (![B_135]: (r1_tarski('#skF_1', k9_relat_1(k2_funct_1('#skF_3'), B_135)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_135) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1606])).
% 4.43/1.82  tff(c_1655, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1629])).
% 4.43/1.82  tff(c_1658, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_1655])).
% 4.43/1.82  tff(c_1662, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1658])).
% 4.43/1.82  tff(c_1733, plain, (![B_139]: (r1_tarski('#skF_1', k9_relat_1(k2_funct_1('#skF_3'), B_139)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_139))), inference(splitRight, [status(thm)], [c_1629])).
% 4.43/1.82  tff(c_1767, plain, (![A_14]: (r1_tarski('#skF_1', k10_relat_1('#skF_3', A_14)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_14) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1733])).
% 4.43/1.82  tff(c_1790, plain, (![A_140]: (r1_tarski('#skF_1', k10_relat_1('#skF_3', A_140)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_140))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1767])).
% 4.43/1.82  tff(c_1828, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_1790])).
% 4.43/1.82  tff(c_1861, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1828])).
% 4.43/1.82  tff(c_141, plain, (![B_34, A_35]: (r1_tarski(k10_relat_1(B_34, k9_relat_1(B_34, A_35)), A_35) | ~v2_funct_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.43/1.82  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.43/1.82  tff(c_149, plain, (![A_3, A_35, B_34]: (r1_tarski(A_3, A_35) | ~r1_tarski(A_3, k10_relat_1(B_34, k9_relat_1(B_34, A_35))) | ~v2_funct_1(B_34) | ~v1_funct_1(B_34) | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_141, c_8])).
% 4.43/1.82  tff(c_1884, plain, (r1_tarski('#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1861, c_149])).
% 4.43/1.82  tff(c_1908, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_1884])).
% 4.43/1.82  tff(c_1910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_1908])).
% 4.43/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.82  
% 4.43/1.82  Inference rules
% 4.43/1.82  ----------------------
% 4.43/1.82  #Ref     : 0
% 4.43/1.82  #Sup     : 481
% 4.43/1.82  #Fact    : 0
% 4.43/1.82  #Define  : 0
% 4.43/1.82  #Split   : 9
% 4.43/1.82  #Chain   : 0
% 4.43/1.82  #Close   : 0
% 4.43/1.82  
% 4.43/1.82  Ordering : KBO
% 4.43/1.82  
% 4.43/1.82  Simplification rules
% 4.43/1.82  ----------------------
% 4.43/1.82  #Subsume      : 158
% 4.43/1.82  #Demod        : 166
% 4.43/1.82  #Tautology    : 40
% 4.43/1.82  #SimpNegUnit  : 1
% 4.43/1.82  #BackRed      : 0
% 4.43/1.82  
% 4.43/1.82  #Partial instantiations: 0
% 4.43/1.82  #Strategies tried      : 1
% 4.43/1.82  
% 4.43/1.82  Timing (in seconds)
% 4.43/1.82  ----------------------
% 4.43/1.83  Preprocessing        : 0.30
% 4.43/1.83  Parsing              : 0.17
% 4.43/1.83  CNF conversion       : 0.02
% 4.43/1.83  Main loop            : 0.70
% 4.43/1.83  Inferencing          : 0.21
% 4.43/1.83  Reduction            : 0.19
% 4.43/1.83  Demodulation         : 0.13
% 4.43/1.83  BG Simplification    : 0.03
% 4.43/1.83  Subsumption          : 0.22
% 4.43/1.83  Abstraction          : 0.04
% 4.43/1.83  MUC search           : 0.00
% 4.43/1.83  Cooper               : 0.00
% 4.43/1.83  Total                : 1.03
% 4.43/1.83  Index Insertion      : 0.00
% 4.43/1.83  Index Deletion       : 0.00
% 4.43/1.83  Index Matching       : 0.00
% 4.43/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------

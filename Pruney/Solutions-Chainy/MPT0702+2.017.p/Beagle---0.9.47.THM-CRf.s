%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:04 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   63 (  98 expanded)
%              Number of leaves         :   25 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :  123 ( 227 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k10_relat_1(B_17,k9_relat_1(B_17,A_16)),A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_20,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_75,plain,(
    ! [B_25,A_26] :
      ( v5_relat_1(B_25,A_26)
      | ~ r1_tarski(k2_relat_1(B_25),A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_78,plain,(
    ! [A_12,A_26] :
      ( v5_relat_1(k6_relat_1(A_12),A_26)
      | ~ r1_tarski(A_12,A_26)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_75])).

tff(c_84,plain,(
    ! [A_12,A_26] :
      ( v5_relat_1(k6_relat_1(A_12),A_26)
      | ~ r1_tarski(A_12,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_78])).

tff(c_34,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_373,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,k10_relat_1(B_65,k9_relat_1(B_65,A_64)))
      | ~ r1_tarski(A_64,k1_relat_1(B_65))
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_760,plain,(
    ! [B_88,A_89] :
      ( k10_relat_1(B_88,k9_relat_1(B_88,A_89)) = A_89
      | ~ r1_tarski(k10_relat_1(B_88,k9_relat_1(B_88,A_89)),A_89)
      | ~ r1_tarski(A_89,k1_relat_1(B_88))
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_373,c_2])).

tff(c_1591,plain,(
    ! [B_134,A_135] :
      ( k10_relat_1(B_134,k9_relat_1(B_134,A_135)) = A_135
      | ~ r1_tarski(A_135,k1_relat_1(B_134))
      | ~ v2_funct_1(B_134)
      | ~ v1_funct_1(B_134)
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_26,c_760])).

tff(c_1605,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1591])).

tff(c_1621,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_1605])).

tff(c_12,plain,(
    ! [C_7,A_5,B_6] :
      ( r1_tarski(k10_relat_1(C_7,A_5),k10_relat_1(C_7,B_6))
      | ~ r1_tarski(A_5,B_6)
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1647,plain,(
    ! [B_6] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_3',B_6))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_6)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_12])).

tff(c_1744,plain,(
    ! [B_137] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_3',B_137))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1647])).

tff(c_1769,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_34,c_1744])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_125,plain,(
    ! [C_35,B_36,A_37] :
      ( v5_relat_1(C_35,B_36)
      | ~ v5_relat_1(C_35,A_37)
      | ~ v1_relat_1(C_35)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_127,plain,(
    ! [A_12,B_36,A_26] :
      ( v5_relat_1(k6_relat_1(A_12),B_36)
      | ~ v1_relat_1(k6_relat_1(A_12))
      | ~ r1_tarski(A_26,B_36)
      | ~ r1_tarski(A_12,A_26) ) ),
    inference(resolution,[status(thm)],[c_84,c_125])).

tff(c_139,plain,(
    ! [A_38,B_39,A_40] :
      ( v5_relat_1(k6_relat_1(A_38),B_39)
      | ~ r1_tarski(A_40,B_39)
      | ~ r1_tarski(A_38,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_127])).

tff(c_400,plain,(
    ! [A_66,A_67,B_68] :
      ( v5_relat_1(k6_relat_1(A_66),A_67)
      | ~ r1_tarski(A_66,k2_relat_1(B_68))
      | ~ v5_relat_1(B_68,A_67)
      | ~ v1_relat_1(B_68) ) ),
    inference(resolution,[status(thm)],[c_10,c_139])).

tff(c_408,plain,(
    ! [A_66,A_67,A_12] :
      ( v5_relat_1(k6_relat_1(A_66),A_67)
      | ~ r1_tarski(A_66,A_12)
      | ~ v5_relat_1(k6_relat_1(A_12),A_67)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_400])).

tff(c_415,plain,(
    ! [A_66,A_67,A_12] :
      ( v5_relat_1(k6_relat_1(A_66),A_67)
      | ~ r1_tarski(A_66,A_12)
      | ~ v5_relat_1(k6_relat_1(A_12),A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_408])).

tff(c_2074,plain,(
    ! [A_144] :
      ( v5_relat_1(k6_relat_1('#skF_1'),A_144)
      | ~ v5_relat_1(k6_relat_1(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))),A_144) ) ),
    inference(resolution,[status(thm)],[c_1769,c_415])).

tff(c_2244,plain,(
    ! [A_146] :
      ( v5_relat_1(k6_relat_1('#skF_1'),A_146)
      | ~ r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')),A_146) ) ),
    inference(resolution,[status(thm)],[c_84,c_2074])).

tff(c_2267,plain,
    ( v5_relat_1(k6_relat_1('#skF_1'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_2244])).

tff(c_2293,plain,(
    v5_relat_1(k6_relat_1('#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_30,c_2267])).

tff(c_86,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k2_relat_1(B_27),A_28)
      | ~ v5_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_12,A_28] :
      ( r1_tarski(A_12,A_28)
      | ~ v5_relat_1(k6_relat_1(A_12),A_28)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_98,plain,(
    ! [A_12,A_28] :
      ( r1_tarski(A_12,A_28)
      | ~ v5_relat_1(k6_relat_1(A_12),A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_2311,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2293,c_98])).

tff(c_2320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.75  
% 3.83/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.76  %$ v5_relat_1 > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.83/1.76  
% 3.83/1.76  %Foreground sorts:
% 3.83/1.76  
% 3.83/1.76  
% 3.83/1.76  %Background operators:
% 3.83/1.76  
% 3.83/1.76  
% 3.83/1.76  %Foreground operators:
% 3.83/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.83/1.76  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.83/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.76  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.83/1.76  tff('#skF_2', type, '#skF_2': $i).
% 3.83/1.76  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.83/1.76  tff('#skF_3', type, '#skF_3': $i).
% 3.83/1.76  tff('#skF_1', type, '#skF_1': $i).
% 3.83/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.83/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.76  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.83/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.83/1.76  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.83/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.83/1.76  
% 3.83/1.78  tff(f_87, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.83/1.78  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 3.83/1.78  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.83/1.78  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.83/1.78  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.83/1.78  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 3.83/1.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.83/1.78  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 3.83/1.78  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 3.83/1.78  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.78  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.78  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.78  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.78  tff(c_26, plain, (![B_17, A_16]: (r1_tarski(k10_relat_1(B_17, k9_relat_1(B_17, A_16)), A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.83/1.78  tff(c_20, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.83/1.78  tff(c_18, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.83/1.78  tff(c_75, plain, (![B_25, A_26]: (v5_relat_1(B_25, A_26) | ~r1_tarski(k2_relat_1(B_25), A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.78  tff(c_78, plain, (![A_12, A_26]: (v5_relat_1(k6_relat_1(A_12), A_26) | ~r1_tarski(A_12, A_26) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_75])).
% 3.83/1.78  tff(c_84, plain, (![A_12, A_26]: (v5_relat_1(k6_relat_1(A_12), A_26) | ~r1_tarski(A_12, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_78])).
% 3.83/1.78  tff(c_34, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.78  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.83/1.78  tff(c_373, plain, (![A_64, B_65]: (r1_tarski(A_64, k10_relat_1(B_65, k9_relat_1(B_65, A_64))) | ~r1_tarski(A_64, k1_relat_1(B_65)) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.83/1.78  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.83/1.78  tff(c_760, plain, (![B_88, A_89]: (k10_relat_1(B_88, k9_relat_1(B_88, A_89))=A_89 | ~r1_tarski(k10_relat_1(B_88, k9_relat_1(B_88, A_89)), A_89) | ~r1_tarski(A_89, k1_relat_1(B_88)) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_373, c_2])).
% 3.83/1.78  tff(c_1591, plain, (![B_134, A_135]: (k10_relat_1(B_134, k9_relat_1(B_134, A_135))=A_135 | ~r1_tarski(A_135, k1_relat_1(B_134)) | ~v2_funct_1(B_134) | ~v1_funct_1(B_134) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_26, c_760])).
% 3.83/1.78  tff(c_1605, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1591])).
% 3.83/1.78  tff(c_1621, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_1605])).
% 3.83/1.78  tff(c_12, plain, (![C_7, A_5, B_6]: (r1_tarski(k10_relat_1(C_7, A_5), k10_relat_1(C_7, B_6)) | ~r1_tarski(A_5, B_6) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.83/1.78  tff(c_1647, plain, (![B_6]: (r1_tarski('#skF_1', k10_relat_1('#skF_3', B_6)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_6) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_12])).
% 3.83/1.78  tff(c_1744, plain, (![B_137]: (r1_tarski('#skF_1', k10_relat_1('#skF_3', B_137)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_137))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1647])).
% 3.83/1.78  tff(c_1769, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(resolution, [status(thm)], [c_34, c_1744])).
% 3.83/1.78  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.78  tff(c_125, plain, (![C_35, B_36, A_37]: (v5_relat_1(C_35, B_36) | ~v5_relat_1(C_35, A_37) | ~v1_relat_1(C_35) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.83/1.78  tff(c_127, plain, (![A_12, B_36, A_26]: (v5_relat_1(k6_relat_1(A_12), B_36) | ~v1_relat_1(k6_relat_1(A_12)) | ~r1_tarski(A_26, B_36) | ~r1_tarski(A_12, A_26))), inference(resolution, [status(thm)], [c_84, c_125])).
% 3.83/1.78  tff(c_139, plain, (![A_38, B_39, A_40]: (v5_relat_1(k6_relat_1(A_38), B_39) | ~r1_tarski(A_40, B_39) | ~r1_tarski(A_38, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_127])).
% 3.83/1.78  tff(c_400, plain, (![A_66, A_67, B_68]: (v5_relat_1(k6_relat_1(A_66), A_67) | ~r1_tarski(A_66, k2_relat_1(B_68)) | ~v5_relat_1(B_68, A_67) | ~v1_relat_1(B_68))), inference(resolution, [status(thm)], [c_10, c_139])).
% 3.83/1.78  tff(c_408, plain, (![A_66, A_67, A_12]: (v5_relat_1(k6_relat_1(A_66), A_67) | ~r1_tarski(A_66, A_12) | ~v5_relat_1(k6_relat_1(A_12), A_67) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_400])).
% 3.83/1.78  tff(c_415, plain, (![A_66, A_67, A_12]: (v5_relat_1(k6_relat_1(A_66), A_67) | ~r1_tarski(A_66, A_12) | ~v5_relat_1(k6_relat_1(A_12), A_67))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_408])).
% 3.83/1.78  tff(c_2074, plain, (![A_144]: (v5_relat_1(k6_relat_1('#skF_1'), A_144) | ~v5_relat_1(k6_relat_1(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))), A_144))), inference(resolution, [status(thm)], [c_1769, c_415])).
% 3.83/1.78  tff(c_2244, plain, (![A_146]: (v5_relat_1(k6_relat_1('#skF_1'), A_146) | ~r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')), A_146))), inference(resolution, [status(thm)], [c_84, c_2074])).
% 3.83/1.78  tff(c_2267, plain, (v5_relat_1(k6_relat_1('#skF_1'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_2244])).
% 3.83/1.78  tff(c_2293, plain, (v5_relat_1(k6_relat_1('#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_30, c_2267])).
% 3.83/1.78  tff(c_86, plain, (![B_27, A_28]: (r1_tarski(k2_relat_1(B_27), A_28) | ~v5_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.83/1.78  tff(c_94, plain, (![A_12, A_28]: (r1_tarski(A_12, A_28) | ~v5_relat_1(k6_relat_1(A_12), A_28) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_86])).
% 3.83/1.78  tff(c_98, plain, (![A_12, A_28]: (r1_tarski(A_12, A_28) | ~v5_relat_1(k6_relat_1(A_12), A_28))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_94])).
% 3.83/1.78  tff(c_2311, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2293, c_98])).
% 3.83/1.78  tff(c_2320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2311])).
% 3.83/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.83/1.78  
% 3.83/1.78  Inference rules
% 3.83/1.78  ----------------------
% 3.83/1.78  #Ref     : 0
% 3.83/1.78  #Sup     : 507
% 3.83/1.78  #Fact    : 0
% 3.83/1.78  #Define  : 0
% 3.83/1.78  #Split   : 9
% 3.83/1.78  #Chain   : 0
% 3.83/1.78  #Close   : 0
% 3.83/1.78  
% 3.83/1.78  Ordering : KBO
% 3.83/1.78  
% 3.83/1.78  Simplification rules
% 3.83/1.78  ----------------------
% 3.83/1.78  #Subsume      : 174
% 3.83/1.78  #Demod        : 254
% 3.83/1.78  #Tautology    : 67
% 3.83/1.78  #SimpNegUnit  : 2
% 3.83/1.78  #BackRed      : 0
% 3.83/1.78  
% 3.83/1.78  #Partial instantiations: 0
% 3.83/1.78  #Strategies tried      : 1
% 3.83/1.78  
% 3.83/1.78  Timing (in seconds)
% 3.83/1.78  ----------------------
% 3.83/1.78  Preprocessing        : 0.28
% 3.83/1.78  Parsing              : 0.15
% 3.83/1.78  CNF conversion       : 0.02
% 3.83/1.78  Main loop            : 0.66
% 3.83/1.78  Inferencing          : 0.21
% 3.83/1.78  Reduction            : 0.21
% 3.83/1.78  Demodulation         : 0.14
% 3.83/1.78  BG Simplification    : 0.02
% 3.83/1.78  Subsumption          : 0.18
% 3.83/1.78  Abstraction          : 0.03
% 4.28/1.78  MUC search           : 0.00
% 4.28/1.78  Cooper               : 0.00
% 4.28/1.78  Total                : 0.98
% 4.28/1.78  Index Insertion      : 0.00
% 4.28/1.78  Index Deletion       : 0.00
% 4.28/1.78  Index Matching       : 0.00
% 4.28/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------

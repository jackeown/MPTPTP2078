%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 147 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( A != k1_xboole_0
          & r1_tarski(A,k1_relat_1(B))
          & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(c_42,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_46,plain,(
    k4_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_20])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_47,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_62,plain,(
    ! [A_8,B_9] : k4_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_47])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    r1_tarski(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    k4_xboole_0(k9_relat_1('#skF_4','#skF_2'),k9_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_47])).

tff(c_14,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [C_16,A_14,B_15] :
      ( k6_subset_1(k9_relat_1(C_16,A_14),k9_relat_1(C_16,B_15)) = k9_relat_1(C_16,k6_subset_1(A_14,B_15))
      | ~ v2_funct_1(C_16)
      | ~ v1_funct_1(C_16)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_325,plain,(
    ! [C_47,A_48,B_49] :
      ( k4_xboole_0(k9_relat_1(C_47,A_48),k9_relat_1(C_47,B_49)) = k9_relat_1(C_47,k4_xboole_0(A_48,B_49))
      | ~ v2_funct_1(C_47)
      | ~ v1_funct_1(C_47)
      | ~ v1_relat_1(C_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_18])).

tff(c_351,plain,
    ( k9_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_325])).

tff(c_359,plain,(
    k9_relat_1('#skF_4',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_351])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_24,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_256,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_288,plain,(
    ! [A_42,B_43,B_44] :
      ( r2_hidden('#skF_1'(A_42,B_43),B_44)
      | ~ r1_tarski(A_42,B_44)
      | r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_256])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_885,plain,(
    ! [A_72,B_73,B_74,B_75] :
      ( r2_hidden('#skF_1'(A_72,B_73),B_74)
      | ~ r1_tarski(B_75,B_74)
      | ~ r1_tarski(A_72,B_75)
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_288,c_2])).

tff(c_979,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),k1_relat_1('#skF_4'))
      | ~ r1_tarski(A_85,'#skF_2')
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_24,c_885])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_988,plain,(
    ! [A_87] :
      ( ~ r1_tarski(A_87,'#skF_2')
      | r1_tarski(A_87,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_979,c_4])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k9_relat_1(B_13,A_12) != k1_xboole_0
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_993,plain,(
    ! [A_87] :
      ( k9_relat_1('#skF_4',A_87) != k1_xboole_0
      | k1_xboole_0 = A_87
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_87,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_988,c_16])).

tff(c_1125,plain,(
    ! [A_91] :
      ( k9_relat_1('#skF_4',A_91) != k1_xboole_0
      | k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_993])).

tff(c_1589,plain,(
    ! [A_102] :
      ( k9_relat_1('#skF_4',A_102) != k1_xboole_0
      | k1_xboole_0 = A_102
      | k4_xboole_0(A_102,'#skF_2') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_1125])).

tff(c_1613,plain,
    ( k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0
    | k4_xboole_0(k4_xboole_0('#skF_2','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_359,c_1589])).

tff(c_1624,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1613])).

tff(c_1626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.57  
% 3.04/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.57  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.04/1.57  
% 3.04/1.57  %Foreground sorts:
% 3.04/1.57  
% 3.04/1.57  
% 3.04/1.57  %Background operators:
% 3.04/1.57  
% 3.04/1.57  
% 3.04/1.57  %Foreground operators:
% 3.04/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.04/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.04/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.04/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.04/1.57  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.04/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.04/1.57  
% 3.04/1.59  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.04/1.59  tff(f_71, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 3.04/1.59  tff(f_38, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.04/1.59  tff(f_40, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.04/1.59  tff(f_58, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 3.04/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.04/1.59  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 3.04/1.59  tff(c_42, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | k4_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.04/1.59  tff(c_20, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.59  tff(c_46, plain, (k4_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_20])).
% 3.04/1.59  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.04/1.59  tff(c_47, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.04/1.59  tff(c_62, plain, (![A_8, B_9]: (k4_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_47])).
% 3.04/1.59  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.59  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.59  tff(c_22, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.59  tff(c_26, plain, (r1_tarski(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.59  tff(c_60, plain, (k4_xboole_0(k9_relat_1('#skF_4', '#skF_2'), k9_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_47])).
% 3.04/1.59  tff(c_14, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.04/1.59  tff(c_18, plain, (![C_16, A_14, B_15]: (k6_subset_1(k9_relat_1(C_16, A_14), k9_relat_1(C_16, B_15))=k9_relat_1(C_16, k6_subset_1(A_14, B_15)) | ~v2_funct_1(C_16) | ~v1_funct_1(C_16) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.04/1.59  tff(c_325, plain, (![C_47, A_48, B_49]: (k4_xboole_0(k9_relat_1(C_47, A_48), k9_relat_1(C_47, B_49))=k9_relat_1(C_47, k4_xboole_0(A_48, B_49)) | ~v2_funct_1(C_47) | ~v1_funct_1(C_47) | ~v1_relat_1(C_47))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_18])).
% 3.04/1.59  tff(c_351, plain, (k9_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0 | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60, c_325])).
% 3.04/1.59  tff(c_359, plain, (k9_relat_1('#skF_4', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_351])).
% 3.04/1.59  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | k4_xboole_0(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.04/1.59  tff(c_24, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.59  tff(c_256, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.59  tff(c_288, plain, (![A_42, B_43, B_44]: (r2_hidden('#skF_1'(A_42, B_43), B_44) | ~r1_tarski(A_42, B_44) | r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_6, c_256])).
% 3.04/1.59  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.59  tff(c_885, plain, (![A_72, B_73, B_74, B_75]: (r2_hidden('#skF_1'(A_72, B_73), B_74) | ~r1_tarski(B_75, B_74) | ~r1_tarski(A_72, B_75) | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_288, c_2])).
% 3.04/1.59  tff(c_979, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), k1_relat_1('#skF_4')) | ~r1_tarski(A_85, '#skF_2') | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_24, c_885])).
% 3.04/1.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.59  tff(c_988, plain, (![A_87]: (~r1_tarski(A_87, '#skF_2') | r1_tarski(A_87, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_979, c_4])).
% 3.04/1.59  tff(c_16, plain, (![B_13, A_12]: (k9_relat_1(B_13, A_12)!=k1_xboole_0 | ~r1_tarski(A_12, k1_relat_1(B_13)) | k1_xboole_0=A_12 | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.04/1.59  tff(c_993, plain, (![A_87]: (k9_relat_1('#skF_4', A_87)!=k1_xboole_0 | k1_xboole_0=A_87 | ~v1_relat_1('#skF_4') | ~r1_tarski(A_87, '#skF_2'))), inference(resolution, [status(thm)], [c_988, c_16])).
% 3.04/1.59  tff(c_1125, plain, (![A_91]: (k9_relat_1('#skF_4', A_91)!=k1_xboole_0 | k1_xboole_0=A_91 | ~r1_tarski(A_91, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_993])).
% 3.04/1.59  tff(c_1589, plain, (![A_102]: (k9_relat_1('#skF_4', A_102)!=k1_xboole_0 | k1_xboole_0=A_102 | k4_xboole_0(A_102, '#skF_2')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1125])).
% 3.04/1.59  tff(c_1613, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_359, c_1589])).
% 3.04/1.59  tff(c_1624, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1613])).
% 3.04/1.59  tff(c_1626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1624])).
% 3.04/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.59  
% 3.04/1.59  Inference rules
% 3.04/1.59  ----------------------
% 3.04/1.59  #Ref     : 0
% 3.04/1.59  #Sup     : 365
% 3.04/1.59  #Fact    : 0
% 3.04/1.59  #Define  : 0
% 3.04/1.59  #Split   : 2
% 3.04/1.59  #Chain   : 0
% 3.04/1.59  #Close   : 0
% 3.04/1.59  
% 3.04/1.59  Ordering : KBO
% 3.04/1.59  
% 3.04/1.59  Simplification rules
% 3.04/1.59  ----------------------
% 3.04/1.59  #Subsume      : 24
% 3.04/1.59  #Demod        : 492
% 3.04/1.59  #Tautology    : 236
% 3.04/1.59  #SimpNegUnit  : 1
% 3.04/1.59  #BackRed      : 0
% 3.04/1.59  
% 3.04/1.59  #Partial instantiations: 0
% 3.04/1.59  #Strategies tried      : 1
% 3.04/1.59  
% 3.04/1.59  Timing (in seconds)
% 3.04/1.59  ----------------------
% 3.04/1.59  Preprocessing        : 0.31
% 3.04/1.59  Parsing              : 0.17
% 3.04/1.59  CNF conversion       : 0.02
% 3.04/1.59  Main loop            : 0.44
% 3.04/1.59  Inferencing          : 0.16
% 3.04/1.59  Reduction            : 0.17
% 3.04/1.59  Demodulation         : 0.13
% 3.04/1.59  BG Simplification    : 0.02
% 3.04/1.59  Subsumption          : 0.07
% 3.04/1.59  Abstraction          : 0.02
% 3.04/1.59  MUC search           : 0.00
% 3.04/1.59  Cooper               : 0.00
% 3.04/1.59  Total                : 0.78
% 3.04/1.59  Index Insertion      : 0.00
% 3.04/1.59  Index Deletion       : 0.00
% 3.04/1.59  Index Matching       : 0.00
% 3.04/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

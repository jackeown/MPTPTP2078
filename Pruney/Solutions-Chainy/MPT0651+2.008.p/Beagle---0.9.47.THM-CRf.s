%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:49 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 133 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  121 ( 354 expanded)
%              Number of equality atoms :   37 ( 129 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_34,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [A_18] :
      ( k1_relat_1(k2_funct_1(A_18)) = k2_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_18] :
      ( k2_relat_1(k2_funct_1(A_18)) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_16] :
      ( v1_relat_1(k2_funct_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_935,plain,(
    ! [A_69,B_70] :
      ( k5_relat_1(k6_relat_1(A_69),B_70) = B_70
      | ~ r1_tarski(k1_relat_1(B_70),A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_948,plain,(
    ! [B_70] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_70)),B_70) = B_70
      | ~ v1_relat_1(B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_935])).

tff(c_1159,plain,(
    ! [B_84,C_85,A_86] :
      ( k2_relat_1(k5_relat_1(B_84,C_85)) = k2_relat_1(k5_relat_1(A_86,C_85))
      | k2_relat_1(B_84) != k2_relat_1(A_86)
      | ~ v1_relat_1(C_85)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1228,plain,(
    ! [A_86,B_70] :
      ( k2_relat_1(k5_relat_1(A_86,B_70)) = k2_relat_1(B_70)
      | k2_relat_1(k6_relat_1(k1_relat_1(B_70))) != k2_relat_1(A_86)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(k6_relat_1(k1_relat_1(B_70)))
      | ~ v1_relat_1(A_86)
      | ~ v1_relat_1(B_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_1159])).

tff(c_1478,plain,(
    ! [A_96,B_97] :
      ( k2_relat_1(k5_relat_1(A_96,B_97)) = k2_relat_1(B_97)
      | k2_relat_1(A_96) != k1_relat_1(B_97)
      | ~ v1_relat_1(A_96)
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14,c_1228])).

tff(c_163,plain,(
    ! [A_36,B_37] :
      ( k1_relat_1(k5_relat_1(A_36,B_37)) = k1_relat_1(A_36)
      | ~ r1_tarski(k2_relat_1(A_36),k1_relat_1(B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_567,plain,(
    ! [A_53,A_54] :
      ( k1_relat_1(k5_relat_1(A_53,k2_funct_1(A_54))) = k1_relat_1(A_53)
      | ~ r1_tarski(k2_relat_1(A_53),k2_relat_1(A_54))
      | ~ v1_relat_1(k2_funct_1(A_54))
      | ~ v1_relat_1(A_53)
      | ~ v2_funct_1(A_54)
      | ~ v1_funct_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_163])).

tff(c_852,plain,(
    ! [A_64] :
      ( k1_relat_1(k5_relat_1(A_64,k2_funct_1(A_64))) = k1_relat_1(A_64)
      | ~ v1_relat_1(k2_funct_1(A_64))
      | ~ v2_funct_1(A_64)
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(resolution,[status(thm)],[c_6,c_567])).

tff(c_30,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_877,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_60])).

tff(c_897,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_877])).

tff(c_907,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_897])).

tff(c_911,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_907])).

tff(c_912,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1509,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1478,c_912])).

tff(c_1553,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1509])).

tff(c_1578,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1553])).

tff(c_1581,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1578])).

tff(c_1585,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1581])).

tff(c_1586,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1553])).

tff(c_1599,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1586])).

tff(c_1602,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1599])).

tff(c_1606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_1602])).

tff(c_1607,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1586])).

tff(c_1611,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1607])).

tff(c_1615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_1611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.57  
% 3.45/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.45/1.57  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.45/1.57  
% 3.45/1.57  %Foreground sorts:
% 3.45/1.57  
% 3.45/1.57  
% 3.45/1.57  %Background operators:
% 3.45/1.57  
% 3.45/1.57  
% 3.45/1.57  %Foreground operators:
% 3.45/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.45/1.57  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.45/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.57  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.45/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.45/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.45/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.45/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.45/1.57  
% 3.72/1.59  tff(f_95, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 3.72/1.59  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.72/1.59  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.72/1.59  tff(f_74, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.72/1.59  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.72/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.72/1.59  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.72/1.59  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 3.72/1.59  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 3.72/1.59  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.72/1.59  tff(c_34, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.72/1.59  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.72/1.59  tff(c_28, plain, (![A_18]: (k1_relat_1(k2_funct_1(A_18))=k2_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.72/1.59  tff(c_26, plain, (![A_18]: (k2_relat_1(k2_funct_1(A_18))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.72/1.59  tff(c_20, plain, (![A_16]: (v1_relat_1(k2_funct_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.72/1.59  tff(c_22, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.72/1.59  tff(c_14, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.72/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.72/1.59  tff(c_935, plain, (![A_69, B_70]: (k5_relat_1(k6_relat_1(A_69), B_70)=B_70 | ~r1_tarski(k1_relat_1(B_70), A_69) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.72/1.59  tff(c_948, plain, (![B_70]: (k5_relat_1(k6_relat_1(k1_relat_1(B_70)), B_70)=B_70 | ~v1_relat_1(B_70))), inference(resolution, [status(thm)], [c_6, c_935])).
% 3.72/1.59  tff(c_1159, plain, (![B_84, C_85, A_86]: (k2_relat_1(k5_relat_1(B_84, C_85))=k2_relat_1(k5_relat_1(A_86, C_85)) | k2_relat_1(B_84)!=k2_relat_1(A_86) | ~v1_relat_1(C_85) | ~v1_relat_1(B_84) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.72/1.59  tff(c_1228, plain, (![A_86, B_70]: (k2_relat_1(k5_relat_1(A_86, B_70))=k2_relat_1(B_70) | k2_relat_1(k6_relat_1(k1_relat_1(B_70)))!=k2_relat_1(A_86) | ~v1_relat_1(B_70) | ~v1_relat_1(k6_relat_1(k1_relat_1(B_70))) | ~v1_relat_1(A_86) | ~v1_relat_1(B_70))), inference(superposition, [status(thm), theory('equality')], [c_948, c_1159])).
% 3.72/1.59  tff(c_1478, plain, (![A_96, B_97]: (k2_relat_1(k5_relat_1(A_96, B_97))=k2_relat_1(B_97) | k2_relat_1(A_96)!=k1_relat_1(B_97) | ~v1_relat_1(A_96) | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14, c_1228])).
% 3.72/1.59  tff(c_163, plain, (![A_36, B_37]: (k1_relat_1(k5_relat_1(A_36, B_37))=k1_relat_1(A_36) | ~r1_tarski(k2_relat_1(A_36), k1_relat_1(B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.72/1.59  tff(c_567, plain, (![A_53, A_54]: (k1_relat_1(k5_relat_1(A_53, k2_funct_1(A_54)))=k1_relat_1(A_53) | ~r1_tarski(k2_relat_1(A_53), k2_relat_1(A_54)) | ~v1_relat_1(k2_funct_1(A_54)) | ~v1_relat_1(A_53) | ~v2_funct_1(A_54) | ~v1_funct_1(A_54) | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_28, c_163])).
% 3.72/1.59  tff(c_852, plain, (![A_64]: (k1_relat_1(k5_relat_1(A_64, k2_funct_1(A_64)))=k1_relat_1(A_64) | ~v1_relat_1(k2_funct_1(A_64)) | ~v2_funct_1(A_64) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(resolution, [status(thm)], [c_6, c_567])).
% 3.72/1.59  tff(c_30, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.72/1.59  tff(c_60, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 3.72/1.59  tff(c_877, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_852, c_60])).
% 3.72/1.59  tff(c_897, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_877])).
% 3.72/1.59  tff(c_907, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_897])).
% 3.72/1.59  tff(c_911, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_907])).
% 3.72/1.59  tff(c_912, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 3.72/1.59  tff(c_1509, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1478, c_912])).
% 3.72/1.59  tff(c_1553, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1509])).
% 3.72/1.59  tff(c_1578, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1553])).
% 3.72/1.59  tff(c_1581, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1578])).
% 3.72/1.59  tff(c_1585, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1581])).
% 3.72/1.59  tff(c_1586, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1553])).
% 3.72/1.59  tff(c_1599, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1586])).
% 3.72/1.59  tff(c_1602, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_1599])).
% 3.72/1.59  tff(c_1606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_1602])).
% 3.72/1.59  tff(c_1607, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1586])).
% 3.72/1.59  tff(c_1611, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1607])).
% 3.72/1.59  tff(c_1615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_1611])).
% 3.72/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.59  
% 3.72/1.59  Inference rules
% 3.72/1.59  ----------------------
% 3.72/1.59  #Ref     : 2
% 3.72/1.59  #Sup     : 343
% 3.72/1.59  #Fact    : 0
% 3.72/1.59  #Define  : 0
% 3.72/1.59  #Split   : 5
% 3.72/1.59  #Chain   : 0
% 3.72/1.59  #Close   : 0
% 3.72/1.59  
% 3.72/1.59  Ordering : KBO
% 3.72/1.59  
% 3.72/1.59  Simplification rules
% 3.72/1.59  ----------------------
% 3.72/1.59  #Subsume      : 28
% 3.72/1.59  #Demod        : 428
% 3.72/1.59  #Tautology    : 147
% 3.72/1.59  #SimpNegUnit  : 0
% 3.72/1.59  #BackRed      : 0
% 3.72/1.59  
% 3.72/1.59  #Partial instantiations: 0
% 3.72/1.59  #Strategies tried      : 1
% 3.72/1.59  
% 3.72/1.59  Timing (in seconds)
% 3.72/1.59  ----------------------
% 3.72/1.59  Preprocessing        : 0.28
% 3.72/1.59  Parsing              : 0.15
% 3.72/1.59  CNF conversion       : 0.02
% 3.72/1.59  Main loop            : 0.58
% 3.72/1.59  Inferencing          : 0.22
% 3.72/1.59  Reduction            : 0.17
% 3.72/1.59  Demodulation         : 0.13
% 3.72/1.59  BG Simplification    : 0.03
% 3.72/1.59  Subsumption          : 0.11
% 3.72/1.59  Abstraction          : 0.04
% 3.72/1.59  MUC search           : 0.00
% 3.72/1.59  Cooper               : 0.00
% 3.72/1.59  Total                : 0.88
% 3.72/1.59  Index Insertion      : 0.00
% 3.72/1.59  Index Deletion       : 0.00
% 3.72/1.59  Index Matching       : 0.00
% 3.72/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

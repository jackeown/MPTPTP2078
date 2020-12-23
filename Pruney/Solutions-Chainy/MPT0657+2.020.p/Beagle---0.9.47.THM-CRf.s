%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:06 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 130 expanded)
%              Number of leaves         :   24 (  58 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 390 expanded)
%              Number of equality atoms :   41 ( 134 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(B) = k1_relat_1(A)
                & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
           => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_30,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_13] : v1_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_93,plain,(
    ! [A_26] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_26)),A_26) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_8)) = k6_relat_1(A_8)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_93])).

tff(c_111,plain,(
    ! [A_8] : k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_8)) = k6_relat_1(A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_105])).

tff(c_6,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_411,plain,(
    ! [B_44,A_45] :
      ( r1_tarski(k2_relat_1(B_44),k1_relat_1(A_45))
      | k1_relat_1(k5_relat_1(B_44,A_45)) != k1_relat_1(B_44)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_429,plain,(
    ! [A_8,A_45] :
      ( r1_tarski(A_8,k1_relat_1(A_45))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_8),A_45)) != k1_relat_1(k6_relat_1(A_8))
      | ~ v1_funct_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8))
      | ~ v1_funct_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_411])).

tff(c_597,plain,(
    ! [A_51,A_52] :
      ( r1_tarski(A_51,k1_relat_1(A_52))
      | k1_relat_1(k5_relat_1(k6_relat_1(A_51),A_52)) != A_51
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_4,c_429])).

tff(c_616,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k1_relat_1(k6_relat_1(A_8)))
      | k1_relat_1(k6_relat_1(A_8)) != A_8
      | ~ v1_funct_1(k6_relat_1(A_8))
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_597])).

tff(c_632,plain,(
    ! [A_53] : r1_tarski(A_53,A_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_4,c_4,c_616])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_34,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_154,plain,(
    ! [B_30,A_31] :
      ( k5_relat_1(B_30,k6_relat_1(A_31)) = B_30
      | ~ r1_tarski(k2_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_166,plain,(
    ! [A_31] :
      ( k5_relat_1('#skF_2',k6_relat_1(A_31)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_31)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_154])).

tff(c_172,plain,(
    ! [A_31] :
      ( k5_relat_1('#skF_2',k6_relat_1(A_31)) = '#skF_2'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_166])).

tff(c_641,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_632,c_172])).

tff(c_28,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k2_funct_1(A_18)) = k6_relat_1(k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_133,plain,(
    ! [A_28] :
      ( k1_relat_1(k2_funct_1(A_28)) = k2_relat_1(A_28)
      | ~ v2_funct_1(A_28)
      | ~ v1_funct_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1190,plain,(
    ! [A_62] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_62)),k2_funct_1(A_62)) = k2_funct_1(A_62)
      | ~ v1_relat_1(k2_funct_1(A_62))
      | ~ v2_funct_1(A_62)
      | ~ v1_funct_1(A_62)
      | ~ v1_relat_1(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_8])).

tff(c_1217,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1190])).

tff(c_1234,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_1217])).

tff(c_1260,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1234])).

tff(c_1263,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_1260])).

tff(c_1267,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1263])).

tff(c_1269,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1234])).

tff(c_1268,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1234])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1306,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1268,c_2])).

tff(c_1320,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_1269,c_1306])).

tff(c_1334,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1320])).

tff(c_1342,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_641,c_1334])).

tff(c_1344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1342])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.62  
% 3.13/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.63  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.13/1.63  
% 3.13/1.63  %Foreground sorts:
% 3.13/1.63  
% 3.13/1.63  
% 3.13/1.63  %Background operators:
% 3.13/1.63  
% 3.13/1.63  
% 3.13/1.63  %Foreground operators:
% 3.13/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.13/1.63  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.13/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.13/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.13/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.13/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.13/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.13/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.63  
% 3.52/1.64  tff(f_112, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 3.52/1.64  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.52/1.64  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.52/1.64  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 3.52/1.64  tff(f_74, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_funct_1)).
% 3.52/1.64  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 3.52/1.64  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 3.52/1.64  tff(f_57, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.52/1.64  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.52/1.64  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 3.52/1.64  tff(c_30, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_44, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_42, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_16, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.52/1.64  tff(c_18, plain, (![A_13]: (v1_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.52/1.64  tff(c_4, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.64  tff(c_93, plain, (![A_26]: (k5_relat_1(k6_relat_1(k1_relat_1(A_26)), A_26)=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.64  tff(c_105, plain, (![A_8]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_8))=k6_relat_1(A_8) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_93])).
% 3.52/1.64  tff(c_111, plain, (![A_8]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_8))=k6_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_105])).
% 3.52/1.64  tff(c_6, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.52/1.64  tff(c_411, plain, (![B_44, A_45]: (r1_tarski(k2_relat_1(B_44), k1_relat_1(A_45)) | k1_relat_1(k5_relat_1(B_44, A_45))!=k1_relat_1(B_44) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.52/1.64  tff(c_429, plain, (![A_8, A_45]: (r1_tarski(A_8, k1_relat_1(A_45)) | k1_relat_1(k5_relat_1(k6_relat_1(A_8), A_45))!=k1_relat_1(k6_relat_1(A_8)) | ~v1_funct_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)) | ~v1_funct_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_6, c_411])).
% 3.52/1.64  tff(c_597, plain, (![A_51, A_52]: (r1_tarski(A_51, k1_relat_1(A_52)) | k1_relat_1(k5_relat_1(k6_relat_1(A_51), A_52))!=A_51 | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_4, c_429])).
% 3.52/1.64  tff(c_616, plain, (![A_8]: (r1_tarski(A_8, k1_relat_1(k6_relat_1(A_8))) | k1_relat_1(k6_relat_1(A_8))!=A_8 | ~v1_funct_1(k6_relat_1(A_8)) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_597])).
% 3.52/1.64  tff(c_632, plain, (![A_53]: (r1_tarski(A_53, A_53))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_4, c_4, c_616])).
% 3.52/1.64  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_34, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_154, plain, (![B_30, A_31]: (k5_relat_1(B_30, k6_relat_1(A_31))=B_30 | ~r1_tarski(k2_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.52/1.64  tff(c_166, plain, (![A_31]: (k5_relat_1('#skF_2', k6_relat_1(A_31))='#skF_2' | ~r1_tarski(k1_relat_1('#skF_1'), A_31) | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_154])).
% 3.52/1.64  tff(c_172, plain, (![A_31]: (k5_relat_1('#skF_2', k6_relat_1(A_31))='#skF_2' | ~r1_tarski(k1_relat_1('#skF_1'), A_31))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_166])).
% 3.52/1.64  tff(c_641, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(resolution, [status(thm)], [c_632, c_172])).
% 3.52/1.64  tff(c_28, plain, (![A_18]: (k5_relat_1(A_18, k2_funct_1(A_18))=k6_relat_1(k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.52/1.64  tff(c_14, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.52/1.64  tff(c_32, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.52/1.64  tff(c_133, plain, (![A_28]: (k1_relat_1(k2_funct_1(A_28))=k2_relat_1(A_28) | ~v2_funct_1(A_28) | ~v1_funct_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.52/1.64  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.52/1.64  tff(c_1190, plain, (![A_62]: (k5_relat_1(k6_relat_1(k2_relat_1(A_62)), k2_funct_1(A_62))=k2_funct_1(A_62) | ~v1_relat_1(k2_funct_1(A_62)) | ~v2_funct_1(A_62) | ~v1_funct_1(A_62) | ~v1_relat_1(A_62))), inference(superposition, [status(thm), theory('equality')], [c_133, c_8])).
% 3.52/1.64  tff(c_1217, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1190])).
% 3.52/1.64  tff(c_1234, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_1217])).
% 3.52/1.64  tff(c_1260, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1234])).
% 3.52/1.64  tff(c_1263, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_14, c_1260])).
% 3.52/1.64  tff(c_1267, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1263])).
% 3.52/1.64  tff(c_1269, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1234])).
% 3.52/1.64  tff(c_1268, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_1234])).
% 3.52/1.64  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.52/1.64  tff(c_1306, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1268, c_2])).
% 3.52/1.64  tff(c_1320, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_1269, c_1306])).
% 3.52/1.64  tff(c_1334, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1320])).
% 3.52/1.64  tff(c_1342, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_641, c_1334])).
% 3.52/1.64  tff(c_1344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1342])).
% 3.52/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.64  
% 3.52/1.64  Inference rules
% 3.52/1.64  ----------------------
% 3.52/1.64  #Ref     : 0
% 3.52/1.64  #Sup     : 276
% 3.52/1.64  #Fact    : 0
% 3.52/1.64  #Define  : 0
% 3.52/1.64  #Split   : 5
% 3.52/1.64  #Chain   : 0
% 3.52/1.64  #Close   : 0
% 3.52/1.64  
% 3.52/1.64  Ordering : KBO
% 3.52/1.64  
% 3.52/1.64  Simplification rules
% 3.52/1.64  ----------------------
% 3.52/1.64  #Subsume      : 15
% 3.52/1.64  #Demod        : 435
% 3.52/1.64  #Tautology    : 152
% 3.52/1.64  #SimpNegUnit  : 2
% 3.52/1.64  #BackRed      : 0
% 3.52/1.64  
% 3.52/1.64  #Partial instantiations: 0
% 3.52/1.64  #Strategies tried      : 1
% 3.52/1.64  
% 3.52/1.64  Timing (in seconds)
% 3.52/1.64  ----------------------
% 3.52/1.64  Preprocessing        : 0.33
% 3.52/1.64  Parsing              : 0.16
% 3.52/1.64  CNF conversion       : 0.02
% 3.52/1.64  Main loop            : 0.50
% 3.52/1.64  Inferencing          : 0.18
% 3.52/1.64  Reduction            : 0.18
% 3.52/1.64  Demodulation         : 0.13
% 3.52/1.64  BG Simplification    : 0.03
% 3.52/1.64  Subsumption          : 0.09
% 3.52/1.64  Abstraction          : 0.03
% 3.52/1.64  MUC search           : 0.00
% 3.52/1.64  Cooper               : 0.00
% 3.52/1.64  Total                : 0.86
% 3.52/1.64  Index Insertion      : 0.00
% 3.52/1.64  Index Deletion       : 0.00
% 3.52/1.64  Index Matching       : 0.00
% 3.52/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------

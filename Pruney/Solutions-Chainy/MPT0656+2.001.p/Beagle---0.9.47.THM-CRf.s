%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:00 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 220 expanded)
%              Number of leaves         :   23 (  91 expanded)
%              Depth                    :   13
%              Number of atoms          :  120 ( 736 expanded)
%              Number of equality atoms :   39 ( 261 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v2_funct_1(A)
                & k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
             => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_26,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_30,plain,(
    k2_relat_1('#skF_1') = k1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_78,plain,(
    ! [A_24] :
      ( k4_relat_1(A_24) = k2_funct_1(A_24)
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_81,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_84,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_81])).

tff(c_10,plain,(
    ! [A_3] :
      ( k1_relat_1(k4_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) = k2_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_10])).

tff(c_106,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) = k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30,c_100])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = B_12
      | ~ r1_tarski(k1_relat_1(B_12),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(A_11),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_11)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_14])).

tff(c_119,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_115])).

tff(c_122,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_119])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_122])).

tff(c_128,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_115])).

tff(c_22,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_244,plain,(
    ! [A_32,B_33,C_34] :
      ( k5_relat_1(k5_relat_1(A_32,B_33),C_34) = k5_relat_1(A_32,k5_relat_1(B_33,C_34))
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_412,plain,(
    ! [A_39,C_40] :
      ( k5_relat_1(k6_relat_1(k2_relat_1(A_39)),C_40) = k5_relat_1(k2_funct_1(A_39),k5_relat_1(A_39,C_40))
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(A_39)
      | ~ v1_relat_1(k2_funct_1(A_39))
      | ~ v2_funct_1(A_39)
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_244])).

tff(c_506,plain,(
    ! [C_40] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_40) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_40))
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v2_funct_1('#skF_1')
      | ~ v1_funct_1('#skF_1')
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_412])).

tff(c_523,plain,(
    ! [C_41] :
      ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),C_41) = k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',C_41))
      | ~ v1_relat_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_128,c_40,c_506])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,(
    ! [A_25,B_26] :
      ( k5_relat_1(k6_relat_1(A_25),B_26) = B_26
      | ~ r1_tarski(k1_relat_1(B_26),A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,(
    ! [B_26] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_26)),B_26) = B_26
      | ~ v1_relat_1(B_26) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_555,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_93])).

tff(c_590,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_555])).

tff(c_28,plain,(
    k6_relat_1(k1_relat_1('#skF_1')) = k5_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_24,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_129,plain,(
    ! [B_27] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_27)),B_27) = B_27
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_138,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_129])).

tff(c_148,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_138])).

tff(c_551,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_148])).

tff(c_588,plain,(
    k5_relat_1(k2_funct_1('#skF_1'),k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_551])).

tff(c_655,plain,
    ( k5_relat_1(k2_funct_1('#skF_1'),k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_588])).

tff(c_663,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_32,c_590,c_28,c_655])).

tff(c_665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_663])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:49:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.46  
% 2.79/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.46  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.79/1.46  
% 2.79/1.46  %Foreground sorts:
% 2.79/1.46  
% 2.79/1.46  
% 2.79/1.46  %Background operators:
% 2.79/1.46  
% 2.79/1.46  
% 2.79/1.46  %Foreground operators:
% 2.79/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.46  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.79/1.46  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.79/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.79/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.79/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.46  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.79/1.46  
% 3.12/1.47  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(A) = k1_relat_1(B))) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_funct_1)).
% 3.12/1.47  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.12/1.47  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.12/1.47  tff(f_37, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 3.12/1.47  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 3.12/1.47  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 3.12/1.47  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.12/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.12/1.47  tff(c_26, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.47  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.47  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.47  tff(c_32, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.47  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.47  tff(c_20, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.12/1.47  tff(c_30, plain, (k2_relat_1('#skF_1')=k1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.47  tff(c_78, plain, (![A_24]: (k4_relat_1(A_24)=k2_funct_1(A_24) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.12/1.47  tff(c_81, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_78])).
% 3.12/1.47  tff(c_84, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_81])).
% 3.12/1.47  tff(c_10, plain, (![A_3]: (k1_relat_1(k4_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.47  tff(c_100, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k2_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_84, c_10])).
% 3.12/1.47  tff(c_106, plain, (k1_relat_1(k2_funct_1('#skF_1'))=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30, c_100])).
% 3.12/1.47  tff(c_14, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=B_12 | ~r1_tarski(k1_relat_1(B_12), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.12/1.47  tff(c_115, plain, (![A_11]: (k5_relat_1(k6_relat_1(A_11), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), A_11) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_106, c_14])).
% 3.12/1.47  tff(c_119, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_115])).
% 3.12/1.47  tff(c_122, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_119])).
% 3.12/1.47  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_122])).
% 3.12/1.47  tff(c_128, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_115])).
% 3.12/1.47  tff(c_22, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.12/1.47  tff(c_244, plain, (![A_32, B_33, C_34]: (k5_relat_1(k5_relat_1(A_32, B_33), C_34)=k5_relat_1(A_32, k5_relat_1(B_33, C_34)) | ~v1_relat_1(C_34) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.12/1.47  tff(c_412, plain, (![A_39, C_40]: (k5_relat_1(k6_relat_1(k2_relat_1(A_39)), C_40)=k5_relat_1(k2_funct_1(A_39), k5_relat_1(A_39, C_40)) | ~v1_relat_1(C_40) | ~v1_relat_1(A_39) | ~v1_relat_1(k2_funct_1(A_39)) | ~v2_funct_1(A_39) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_22, c_244])).
% 3.12/1.47  tff(c_506, plain, (![C_40]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_40)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_40)) | ~v1_relat_1(C_40) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_412])).
% 3.12/1.47  tff(c_523, plain, (![C_41]: (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), C_41)=k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', C_41)) | ~v1_relat_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_128, c_40, c_506])).
% 3.12/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.47  tff(c_85, plain, (![A_25, B_26]: (k5_relat_1(k6_relat_1(A_25), B_26)=B_26 | ~r1_tarski(k1_relat_1(B_26), A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.12/1.47  tff(c_93, plain, (![B_26]: (k5_relat_1(k6_relat_1(k1_relat_1(B_26)), B_26)=B_26 | ~v1_relat_1(B_26))), inference(resolution, [status(thm)], [c_6, c_85])).
% 3.12/1.47  tff(c_555, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_523, c_93])).
% 3.12/1.47  tff(c_590, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_555])).
% 3.12/1.47  tff(c_28, plain, (k6_relat_1(k1_relat_1('#skF_1'))=k5_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.12/1.47  tff(c_24, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.12/1.47  tff(c_129, plain, (![B_27]: (k5_relat_1(k6_relat_1(k1_relat_1(B_27)), B_27)=B_27 | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_6, c_85])).
% 3.12/1.47  tff(c_138, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_129])).
% 3.12/1.47  tff(c_148, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_2')), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_138])).
% 3.12/1.47  tff(c_551, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_523, c_148])).
% 3.12/1.47  tff(c_588, plain, (k5_relat_1(k2_funct_1('#skF_1'), k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_128, c_551])).
% 3.12/1.47  tff(c_655, plain, (k5_relat_1(k2_funct_1('#skF_1'), k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_588])).
% 3.12/1.47  tff(c_663, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_32, c_590, c_28, c_655])).
% 3.12/1.47  tff(c_665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_663])).
% 3.12/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.47  
% 3.12/1.47  Inference rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Ref     : 0
% 3.12/1.47  #Sup     : 148
% 3.12/1.47  #Fact    : 0
% 3.12/1.47  #Define  : 0
% 3.12/1.47  #Split   : 6
% 3.12/1.47  #Chain   : 0
% 3.12/1.47  #Close   : 0
% 3.12/1.47  
% 3.12/1.47  Ordering : KBO
% 3.12/1.47  
% 3.12/1.47  Simplification rules
% 3.12/1.47  ----------------------
% 3.12/1.47  #Subsume      : 17
% 3.12/1.47  #Demod        : 119
% 3.12/1.47  #Tautology    : 64
% 3.12/1.47  #SimpNegUnit  : 1
% 3.12/1.47  #BackRed      : 0
% 3.12/1.47  
% 3.12/1.47  #Partial instantiations: 0
% 3.12/1.47  #Strategies tried      : 1
% 3.12/1.47  
% 3.12/1.47  Timing (in seconds)
% 3.12/1.47  ----------------------
% 3.12/1.48  Preprocessing        : 0.32
% 3.12/1.48  Parsing              : 0.18
% 3.12/1.48  CNF conversion       : 0.02
% 3.12/1.48  Main loop            : 0.34
% 3.12/1.48  Inferencing          : 0.13
% 3.12/1.48  Reduction            : 0.11
% 3.12/1.48  Demodulation         : 0.08
% 3.12/1.48  BG Simplification    : 0.02
% 3.12/1.48  Subsumption          : 0.07
% 3.12/1.48  Abstraction          : 0.02
% 3.12/1.48  MUC search           : 0.00
% 3.12/1.48  Cooper               : 0.00
% 3.12/1.48  Total                : 0.70
% 3.12/1.48  Index Insertion      : 0.00
% 3.12/1.48  Index Deletion       : 0.00
% 3.12/1.48  Index Matching       : 0.00
% 3.12/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

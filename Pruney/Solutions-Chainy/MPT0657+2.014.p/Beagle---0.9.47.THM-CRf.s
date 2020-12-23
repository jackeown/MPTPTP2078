%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:06 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 163 expanded)
%              Number of leaves         :   25 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  104 ( 505 expanded)
%              Number of equality atoms :   36 ( 183 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_48,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_32,plain,(
    k2_funct_1('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    k2_relat_1('#skF_2') = k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_87,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k6_relat_1(k2_relat_1(A_27))) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_99,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_87])).

tff(c_105,plain,(
    k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_99])).

tff(c_30,plain,(
    ! [A_21] :
      ( k5_relat_1(A_21,k2_funct_1(A_21)) = k6_relat_1(k1_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_26,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_57,plain,(
    v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_160,plain,(
    ! [A_36] :
      ( k4_relat_1(A_36) = k2_funct_1(A_36)
      | ~ v2_funct_1(A_36)
      | ~ v1_funct_1(A_36)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_166,plain,
    ( k4_relat_1('#skF_1') = k2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_160])).

tff(c_170,plain,(
    k4_relat_1('#skF_1') = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_166])).

tff(c_96,plain,
    ( k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_87])).

tff(c_103,plain,(
    k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_96])).

tff(c_61,plain,(
    ! [A_25] : k4_relat_1(k6_relat_1(A_25)) = k6_relat_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_70,plain,(
    k6_relat_1(k2_relat_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_61])).

tff(c_73,plain,(
    k4_relat_1(k5_relat_1('#skF_2','#skF_1')) = k5_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_238,plain,(
    ! [B_39,A_40] :
      ( k5_relat_1(k4_relat_1(B_39),k4_relat_1(A_40)) = k4_relat_1(k5_relat_1(A_40,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_250,plain,(
    ! [B_39] :
      ( k5_relat_1(k4_relat_1(B_39),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_238])).

tff(c_351,plain,(
    ! [B_44] :
      ( k5_relat_1(k4_relat_1(B_44),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_250])).

tff(c_363,plain,
    ( k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k4_relat_1(k5_relat_1('#skF_1',k5_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k5_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_351])).

tff(c_372,plain,(
    k5_relat_1(k5_relat_1('#skF_2','#skF_1'),k2_funct_1('#skF_1')) = k2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_170,c_103,c_363])).

tff(c_479,plain,(
    ! [A_50,B_51,C_52] :
      ( k5_relat_1(k5_relat_1(A_50,B_51),C_52) = k5_relat_1(A_50,k5_relat_1(B_51,C_52))
      | ~ v1_relat_1(C_52)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_517,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_479])).

tff(c_583,plain,
    ( k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_517])).

tff(c_1050,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_583])).

tff(c_1053,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1050])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_1053])).

tff(c_1058,plain,(
    k5_relat_1('#skF_2',k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k2_funct_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_583])).

tff(c_1067,plain,
    ( k5_relat_1('#skF_2',k6_relat_1(k1_relat_1('#skF_1'))) = k2_funct_1('#skF_1')
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1058])).

tff(c_1073,plain,(
    k2_funct_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_38,c_105,c_1067])).

tff(c_1075,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1073])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:19:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  
% 2.89/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.45  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.89/1.45  
% 2.89/1.45  %Foreground sorts:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Background operators:
% 2.89/1.45  
% 2.89/1.45  
% 2.89/1.45  %Foreground operators:
% 2.89/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.89/1.45  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.89/1.45  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.89/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.89/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.89/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.89/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.89/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.89/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.89/1.45  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.89/1.45  
% 3.23/1.46  tff(f_112, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 3.23/1.46  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.23/1.46  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 3.23/1.46  tff(f_84, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 3.23/1.46  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.23/1.46  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 3.23/1.46  tff(f_48, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 3.23/1.46  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.23/1.46  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 3.23/1.46  tff(c_32, plain, (k2_funct_1('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.46  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.46  tff(c_44, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.46  tff(c_38, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.46  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.46  tff(c_36, plain, (k2_relat_1('#skF_2')=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.46  tff(c_87, plain, (![A_27]: (k5_relat_1(A_27, k6_relat_1(k2_relat_1(A_27)))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.23/1.46  tff(c_99, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_36, c_87])).
% 3.23/1.46  tff(c_105, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_99])).
% 3.23/1.46  tff(c_30, plain, (![A_21]: (k5_relat_1(A_21, k2_funct_1(A_21))=k6_relat_1(k1_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.23/1.46  tff(c_26, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.46  tff(c_34, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.23/1.46  tff(c_18, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.23/1.46  tff(c_57, plain, (v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_18])).
% 3.23/1.46  tff(c_160, plain, (![A_36]: (k4_relat_1(A_36)=k2_funct_1(A_36) | ~v2_funct_1(A_36) | ~v1_funct_1(A_36) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.23/1.46  tff(c_166, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_160])).
% 3.23/1.46  tff(c_170, plain, (k4_relat_1('#skF_1')=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_166])).
% 3.23/1.46  tff(c_96, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_87])).
% 3.23/1.46  tff(c_103, plain, (k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_96])).
% 3.23/1.46  tff(c_61, plain, (![A_25]: (k4_relat_1(k6_relat_1(A_25))=k6_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.23/1.46  tff(c_70, plain, (k6_relat_1(k2_relat_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_61])).
% 3.23/1.46  tff(c_73, plain, (k4_relat_1(k5_relat_1('#skF_2', '#skF_1'))=k5_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 3.23/1.46  tff(c_238, plain, (![B_39, A_40]: (k5_relat_1(k4_relat_1(B_39), k4_relat_1(A_40))=k4_relat_1(k5_relat_1(A_40, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.23/1.46  tff(c_250, plain, (![B_39]: (k5_relat_1(k4_relat_1(B_39), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_170, c_238])).
% 3.23/1.46  tff(c_351, plain, (![B_44]: (k5_relat_1(k4_relat_1(B_44), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', B_44)) | ~v1_relat_1(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_250])).
% 3.23/1.46  tff(c_363, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k4_relat_1(k5_relat_1('#skF_1', k5_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k5_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_73, c_351])).
% 3.23/1.46  tff(c_372, plain, (k5_relat_1(k5_relat_1('#skF_2', '#skF_1'), k2_funct_1('#skF_1'))=k2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_170, c_103, c_363])).
% 3.23/1.46  tff(c_479, plain, (![A_50, B_51, C_52]: (k5_relat_1(k5_relat_1(A_50, B_51), C_52)=k5_relat_1(A_50, k5_relat_1(B_51, C_52)) | ~v1_relat_1(C_52) | ~v1_relat_1(B_51) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.46  tff(c_517, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_372, c_479])).
% 3.23/1.46  tff(c_583, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_517])).
% 3.23/1.46  tff(c_1050, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_583])).
% 3.23/1.46  tff(c_1053, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1050])).
% 3.23/1.46  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_1053])).
% 3.23/1.46  tff(c_1058, plain, (k5_relat_1('#skF_2', k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k2_funct_1('#skF_1')), inference(splitRight, [status(thm)], [c_583])).
% 3.23/1.46  tff(c_1067, plain, (k5_relat_1('#skF_2', k6_relat_1(k1_relat_1('#skF_1')))=k2_funct_1('#skF_1') | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1058])).
% 3.23/1.46  tff(c_1073, plain, (k2_funct_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_38, c_105, c_1067])).
% 3.23/1.46  tff(c_1075, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1073])).
% 3.23/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.46  
% 3.23/1.46  Inference rules
% 3.23/1.46  ----------------------
% 3.23/1.46  #Ref     : 1
% 3.23/1.46  #Sup     : 235
% 3.23/1.46  #Fact    : 0
% 3.23/1.46  #Define  : 0
% 3.23/1.46  #Split   : 1
% 3.23/1.46  #Chain   : 0
% 3.23/1.46  #Close   : 0
% 3.23/1.46  
% 3.23/1.46  Ordering : KBO
% 3.23/1.46  
% 3.23/1.46  Simplification rules
% 3.23/1.46  ----------------------
% 3.23/1.46  #Subsume      : 0
% 3.23/1.46  #Demod        : 213
% 3.23/1.47  #Tautology    : 124
% 3.23/1.47  #SimpNegUnit  : 1
% 3.23/1.47  #BackRed      : 2
% 3.23/1.47  
% 3.23/1.47  #Partial instantiations: 0
% 3.23/1.47  #Strategies tried      : 1
% 3.23/1.47  
% 3.23/1.47  Timing (in seconds)
% 3.23/1.47  ----------------------
% 3.23/1.47  Preprocessing        : 0.31
% 3.23/1.47  Parsing              : 0.17
% 3.23/1.47  CNF conversion       : 0.02
% 3.23/1.47  Main loop            : 0.38
% 3.23/1.47  Inferencing          : 0.14
% 3.23/1.47  Reduction            : 0.14
% 3.23/1.47  Demodulation         : 0.10
% 3.23/1.47  BG Simplification    : 0.02
% 3.23/1.47  Subsumption          : 0.06
% 3.23/1.47  Abstraction          : 0.02
% 3.23/1.47  MUC search           : 0.00
% 3.23/1.47  Cooper               : 0.00
% 3.23/1.47  Total                : 0.72
% 3.23/1.47  Index Insertion      : 0.00
% 3.23/1.47  Index Deletion       : 0.00
% 3.23/1.47  Index Matching       : 0.00
% 3.23/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

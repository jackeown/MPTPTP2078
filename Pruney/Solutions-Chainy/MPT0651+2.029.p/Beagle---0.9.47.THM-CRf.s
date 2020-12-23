%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:51 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 180 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  134 ( 501 expanded)
%              Number of equality atoms :   50 ( 205 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_26,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_22,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_18] :
      ( k5_relat_1(A_18,k6_relat_1(k2_relat_1(A_18))) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_277,plain,(
    ! [C_38,B_39,A_40] :
      ( k1_relat_1(k5_relat_1(C_38,B_39)) = k1_relat_1(k5_relat_1(C_38,A_40))
      | k1_relat_1(B_39) != k1_relat_1(A_40)
      | ~ v1_relat_1(C_38)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_319,plain,(
    ! [A_18,B_39] :
      ( k1_relat_1(k5_relat_1(A_18,B_39)) = k1_relat_1(A_18)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_18))) != k1_relat_1(B_39)
      | ~ v1_relat_1(A_18)
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_277])).

tff(c_399,plain,(
    ! [A_43,B_44] :
      ( k1_relat_1(k5_relat_1(A_43,B_44)) = k1_relat_1(A_43)
      | k2_relat_1(A_43) != k1_relat_1(B_44)
      | ~ v1_relat_1(B_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_319])).

tff(c_24,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_415,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_66])).

tff(c_445,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_415])).

tff(c_456,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_459,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_456])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_459])).

tff(c_464,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_468,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_464])).

tff(c_472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_468])).

tff(c_474,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_549,plain,(
    ! [C_50,B_51,A_52] :
      ( k1_relat_1(k5_relat_1(C_50,B_51)) = k1_relat_1(k5_relat_1(C_50,A_52))
      | k1_relat_1(B_51) != k1_relat_1(A_52)
      | ~ v1_relat_1(C_50)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_612,plain,(
    ! [A_52] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_52)) = k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(A_52)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_549])).

tff(c_639,plain,(
    ! [A_52] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_52)) = k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(A_52)
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_612])).

tff(c_773,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_776,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_773])).

tff(c_780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_776])).

tff(c_782,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_10,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_17] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_17)),A_17) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_783,plain,(
    ! [B_57,C_58,A_59] :
      ( k2_relat_1(k5_relat_1(B_57,C_58)) = k2_relat_1(k5_relat_1(A_59,C_58))
      | k2_relat_1(B_57) != k2_relat_1(A_59)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_473,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_804,plain,(
    ! [B_57] :
      ( k2_relat_1(k5_relat_1(B_57,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(B_57) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_783,c_473])).

tff(c_918,plain,(
    ! [B_62] :
      ( k2_relat_1(k5_relat_1(B_62,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(B_62) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_782,c_804])).

tff(c_930,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k2_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1')))) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_918])).

tff(c_936,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_2,c_10,c_930])).

tff(c_937,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_936])).

tff(c_940,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_937])).

tff(c_944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_940])).

tff(c_945,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_936])).

tff(c_949,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_945])).

tff(c_953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_949])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:46:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.41  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.86/1.41  
% 2.86/1.41  %Foreground sorts:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Background operators:
% 2.86/1.41  
% 2.86/1.41  
% 2.86/1.41  %Foreground operators:
% 2.86/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.86/1.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.86/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.41  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.86/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.41  
% 2.86/1.42  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.86/1.42  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.86/1.42  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.86/1.42  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.86/1.42  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.86/1.42  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.86/1.42  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 2.86/1.42  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 2.86/1.42  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 2.86/1.42  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.42  tff(c_28, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.42  tff(c_26, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.42  tff(c_20, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.86/1.42  tff(c_22, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.86/1.42  tff(c_18, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.42  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.42  tff(c_8, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.42  tff(c_14, plain, (![A_18]: (k5_relat_1(A_18, k6_relat_1(k2_relat_1(A_18)))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.86/1.42  tff(c_277, plain, (![C_38, B_39, A_40]: (k1_relat_1(k5_relat_1(C_38, B_39))=k1_relat_1(k5_relat_1(C_38, A_40)) | k1_relat_1(B_39)!=k1_relat_1(A_40) | ~v1_relat_1(C_38) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.42  tff(c_319, plain, (![A_18, B_39]: (k1_relat_1(k5_relat_1(A_18, B_39))=k1_relat_1(A_18) | k1_relat_1(k6_relat_1(k2_relat_1(A_18)))!=k1_relat_1(B_39) | ~v1_relat_1(A_18) | ~v1_relat_1(B_39) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(superposition, [status(thm), theory('equality')], [c_14, c_277])).
% 2.86/1.42  tff(c_399, plain, (![A_43, B_44]: (k1_relat_1(k5_relat_1(A_43, B_44))=k1_relat_1(A_43) | k2_relat_1(A_43)!=k1_relat_1(B_44) | ~v1_relat_1(B_44) | ~v1_relat_1(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_319])).
% 2.86/1.42  tff(c_24, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.42  tff(c_66, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.86/1.42  tff(c_415, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_399, c_66])).
% 2.86/1.42  tff(c_445, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_415])).
% 2.86/1.42  tff(c_456, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_445])).
% 2.86/1.42  tff(c_459, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_456])).
% 2.86/1.42  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_459])).
% 2.86/1.42  tff(c_464, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_445])).
% 2.86/1.42  tff(c_468, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_464])).
% 2.86/1.42  tff(c_472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_468])).
% 2.86/1.42  tff(c_474, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.86/1.42  tff(c_549, plain, (![C_50, B_51, A_52]: (k1_relat_1(k5_relat_1(C_50, B_51))=k1_relat_1(k5_relat_1(C_50, A_52)) | k1_relat_1(B_51)!=k1_relat_1(A_52) | ~v1_relat_1(C_50) | ~v1_relat_1(B_51) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.42  tff(c_612, plain, (![A_52]: (k1_relat_1(k5_relat_1('#skF_1', A_52))=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(A_52) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_474, c_549])).
% 2.86/1.42  tff(c_639, plain, (![A_52]: (k1_relat_1(k5_relat_1('#skF_1', A_52))=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(A_52) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_612])).
% 2.86/1.42  tff(c_773, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_639])).
% 2.86/1.42  tff(c_776, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_773])).
% 2.86/1.42  tff(c_780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_776])).
% 2.86/1.42  tff(c_782, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_639])).
% 2.86/1.42  tff(c_10, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.42  tff(c_12, plain, (![A_17]: (k5_relat_1(k6_relat_1(k1_relat_1(A_17)), A_17)=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.86/1.42  tff(c_783, plain, (![B_57, C_58, A_59]: (k2_relat_1(k5_relat_1(B_57, C_58))=k2_relat_1(k5_relat_1(A_59, C_58)) | k2_relat_1(B_57)!=k2_relat_1(A_59) | ~v1_relat_1(C_58) | ~v1_relat_1(B_57) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.86/1.42  tff(c_473, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.86/1.42  tff(c_804, plain, (![B_57]: (k2_relat_1(k5_relat_1(B_57, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(B_57)!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_57) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_783, c_473])).
% 2.86/1.42  tff(c_918, plain, (![B_62]: (k2_relat_1(k5_relat_1(B_62, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(B_62)!=k2_relat_1('#skF_1') | ~v1_relat_1(B_62))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_782, c_804])).
% 2.86/1.42  tff(c_930, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k2_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))))!=k2_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_918])).
% 2.86/1.42  tff(c_936, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_2, c_10, c_930])).
% 2.86/1.42  tff(c_937, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_936])).
% 2.86/1.42  tff(c_940, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_937])).
% 2.86/1.42  tff(c_944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_940])).
% 2.86/1.42  tff(c_945, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_936])).
% 2.86/1.42  tff(c_949, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20, c_945])).
% 2.86/1.42  tff(c_953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_949])).
% 2.86/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  Inference rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Ref     : 0
% 2.86/1.42  #Sup     : 206
% 2.86/1.42  #Fact    : 0
% 2.86/1.42  #Define  : 0
% 2.86/1.42  #Split   : 5
% 2.86/1.42  #Chain   : 0
% 2.86/1.42  #Close   : 0
% 2.86/1.42  
% 2.86/1.42  Ordering : KBO
% 2.86/1.42  
% 2.86/1.42  Simplification rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Subsume      : 8
% 2.86/1.42  #Demod        : 202
% 2.86/1.42  #Tautology    : 72
% 2.86/1.42  #SimpNegUnit  : 0
% 2.86/1.42  #BackRed      : 0
% 2.86/1.42  
% 2.86/1.42  #Partial instantiations: 0
% 2.86/1.42  #Strategies tried      : 1
% 2.86/1.42  
% 2.86/1.42  Timing (in seconds)
% 2.86/1.42  ----------------------
% 2.86/1.42  Preprocessing        : 0.29
% 2.86/1.42  Parsing              : 0.16
% 2.86/1.42  CNF conversion       : 0.02
% 2.86/1.42  Main loop            : 0.36
% 2.86/1.42  Inferencing          : 0.14
% 2.86/1.42  Reduction            : 0.11
% 2.86/1.42  Demodulation         : 0.08
% 2.86/1.42  BG Simplification    : 0.02
% 2.86/1.42  Subsumption          : 0.06
% 2.86/1.42  Abstraction          : 0.03
% 2.86/1.42  MUC search           : 0.00
% 2.86/1.42  Cooper               : 0.00
% 2.86/1.42  Total                : 0.68
% 2.86/1.42  Index Insertion      : 0.00
% 2.86/1.42  Index Deletion       : 0.00
% 2.86/1.42  Index Matching       : 0.00
% 2.86/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:03:51 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 182 expanded)
%              Number of leaves         :   21 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  139 ( 513 expanded)
%              Number of equality atoms :   52 ( 209 expanded)
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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k1_relat_1(A) = k1_relat_1(B)
               => k1_relat_1(k5_relat_1(C,A)) = k1_relat_1(k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_28,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    ! [A_20] :
      ( k1_relat_1(k2_funct_1(A_20)) = k2_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_16,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_587,plain,(
    ! [C_50,B_51,A_52] :
      ( k1_relat_1(k5_relat_1(C_50,B_51)) = k1_relat_1(k5_relat_1(C_50,A_52))
      | k1_relat_1(B_51) != k1_relat_1(A_52)
      | ~ v1_relat_1(C_50)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_relat_1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ! [C_35,B_36,A_37] :
      ( k1_relat_1(k5_relat_1(C_35,B_36)) = k1_relat_1(k5_relat_1(C_35,A_37))
      | k1_relat_1(B_36) != k1_relat_1(A_37)
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_235,plain,(
    ! [A_17,A_37] :
      ( k1_relat_1(k5_relat_1(A_17,A_37)) = k1_relat_1(A_17)
      | k1_relat_1(k6_relat_1(k2_relat_1(A_17))) != k1_relat_1(A_37)
      | ~ v1_relat_1(A_17)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_17)))
      | ~ v1_relat_1(A_37)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_160])).

tff(c_327,plain,(
    ! [A_40,A_41] :
      ( k1_relat_1(k5_relat_1(A_40,A_41)) = k1_relat_1(A_40)
      | k2_relat_1(A_40) != k1_relat_1(A_41)
      | ~ v1_relat_1(A_41)
      | ~ v1_relat_1(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_235])).

tff(c_26,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_55,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_349,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_55])).

tff(c_385,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_349])).

tff(c_403,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_385])).

tff(c_406,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_403])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_406])).

tff(c_411,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_385])).

tff(c_512,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_411])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_512])).

tff(c_518,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) = k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_611,plain,(
    ! [A_52] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_52)) = k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(A_52)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_518])).

tff(c_651,plain,(
    ! [A_52] :
      ( k1_relat_1(k5_relat_1('#skF_1',A_52)) = k1_relat_1('#skF_1')
      | k1_relat_1(k2_funct_1('#skF_1')) != k1_relat_1(A_52)
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_611])).

tff(c_783,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_651])).

tff(c_786,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_783])).

tff(c_790,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_786])).

tff(c_792,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_651])).

tff(c_8,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_793,plain,(
    ! [B_57,C_58,A_59] :
      ( k2_relat_1(k5_relat_1(B_57,C_58)) = k2_relat_1(k5_relat_1(A_59,C_58))
      | k2_relat_1(B_57) != k2_relat_1(A_59)
      | ~ v1_relat_1(C_58)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_517,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_817,plain,(
    ! [A_59] :
      ( k2_relat_1(k5_relat_1(A_59,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(A_59) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_517])).

tff(c_851,plain,(
    ! [A_59] :
      ( k2_relat_1(k5_relat_1(A_59,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(A_59) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_817])).

tff(c_917,plain,(
    ! [A_62] :
      ( k2_relat_1(k5_relat_1(A_62,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(A_62) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_851])).

tff(c_929,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k2_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1')))) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_917])).

tff(c_935,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_18,c_8,c_929])).

tff(c_936,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_935])).

tff(c_939,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_936])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_939])).

tff(c_944,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_935])).

tff(c_948,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_944])).

tff(c_952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:17:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.41  
% 2.75/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.42  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 2.96/1.42  
% 2.96/1.42  %Foreground sorts:
% 2.96/1.42  
% 2.96/1.42  
% 2.96/1.42  %Background operators:
% 2.96/1.42  
% 2.96/1.42  
% 2.96/1.42  %Foreground operators:
% 2.96/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.42  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.96/1.42  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.96/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.96/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.96/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.42  
% 2.96/1.43  tff(f_94, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 2.96/1.43  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 2.96/1.43  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 2.96/1.43  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 2.96/1.43  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.96/1.43  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.96/1.43  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 2.96/1.43  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 2.96/1.43  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 2.96/1.43  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.96/1.43  tff(c_30, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.96/1.43  tff(c_28, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.96/1.43  tff(c_22, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.43  tff(c_24, plain, (![A_20]: (k1_relat_1(k2_funct_1(A_20))=k2_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.96/1.43  tff(c_16, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.96/1.43  tff(c_587, plain, (![C_50, B_51, A_52]: (k1_relat_1(k5_relat_1(C_50, B_51))=k1_relat_1(k5_relat_1(C_50, A_52)) | k1_relat_1(B_51)!=k1_relat_1(A_52) | ~v1_relat_1(C_50) | ~v1_relat_1(B_51) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.43  tff(c_18, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.96/1.43  tff(c_6, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.96/1.43  tff(c_12, plain, (![A_17]: (k5_relat_1(A_17, k6_relat_1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.43  tff(c_160, plain, (![C_35, B_36, A_37]: (k1_relat_1(k5_relat_1(C_35, B_36))=k1_relat_1(k5_relat_1(C_35, A_37)) | k1_relat_1(B_36)!=k1_relat_1(A_37) | ~v1_relat_1(C_35) | ~v1_relat_1(B_36) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.96/1.43  tff(c_235, plain, (![A_17, A_37]: (k1_relat_1(k5_relat_1(A_17, A_37))=k1_relat_1(A_17) | k1_relat_1(k6_relat_1(k2_relat_1(A_17)))!=k1_relat_1(A_37) | ~v1_relat_1(A_17) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_17))) | ~v1_relat_1(A_37) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_160])).
% 2.96/1.43  tff(c_327, plain, (![A_40, A_41]: (k1_relat_1(k5_relat_1(A_40, A_41))=k1_relat_1(A_40) | k2_relat_1(A_40)!=k1_relat_1(A_41) | ~v1_relat_1(A_41) | ~v1_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_235])).
% 2.96/1.43  tff(c_26, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.96/1.43  tff(c_55, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.96/1.43  tff(c_349, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_327, c_55])).
% 2.96/1.43  tff(c_385, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_349])).
% 2.96/1.43  tff(c_403, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_385])).
% 2.96/1.43  tff(c_406, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_403])).
% 2.96/1.43  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_406])).
% 2.96/1.43  tff(c_411, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_385])).
% 2.96/1.43  tff(c_512, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_411])).
% 2.96/1.43  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_512])).
% 2.96/1.43  tff(c_518, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.96/1.43  tff(c_611, plain, (![A_52]: (k1_relat_1(k5_relat_1('#skF_1', A_52))=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(A_52) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_587, c_518])).
% 2.96/1.43  tff(c_651, plain, (![A_52]: (k1_relat_1(k5_relat_1('#skF_1', A_52))=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1(A_52) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_611])).
% 2.96/1.43  tff(c_783, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_651])).
% 2.96/1.43  tff(c_786, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_783])).
% 2.96/1.43  tff(c_790, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_786])).
% 2.96/1.43  tff(c_792, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_651])).
% 2.96/1.43  tff(c_8, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.96/1.43  tff(c_10, plain, (![A_16]: (k5_relat_1(k6_relat_1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.96/1.43  tff(c_793, plain, (![B_57, C_58, A_59]: (k2_relat_1(k5_relat_1(B_57, C_58))=k2_relat_1(k5_relat_1(A_59, C_58)) | k2_relat_1(B_57)!=k2_relat_1(A_59) | ~v1_relat_1(C_58) | ~v1_relat_1(B_57) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.96/1.43  tff(c_517, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.96/1.43  tff(c_817, plain, (![A_59]: (k2_relat_1(k5_relat_1(A_59, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(A_59)!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_793, c_517])).
% 2.96/1.43  tff(c_851, plain, (![A_59]: (k2_relat_1(k5_relat_1(A_59, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(A_59)!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_817])).
% 2.96/1.43  tff(c_917, plain, (![A_62]: (k2_relat_1(k5_relat_1(A_62, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(A_62)!=k2_relat_1('#skF_1') | ~v1_relat_1(A_62))), inference(demodulation, [status(thm), theory('equality')], [c_792, c_851])).
% 2.96/1.43  tff(c_929, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k2_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1'))))!=k2_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k1_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_917])).
% 2.96/1.43  tff(c_935, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_792, c_18, c_8, c_929])).
% 2.96/1.43  tff(c_936, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_935])).
% 2.96/1.43  tff(c_939, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_936])).
% 2.96/1.43  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_939])).
% 2.96/1.43  tff(c_944, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_935])).
% 2.96/1.43  tff(c_948, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_22, c_944])).
% 2.96/1.43  tff(c_952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_948])).
% 2.96/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.43  
% 2.96/1.43  Inference rules
% 2.96/1.43  ----------------------
% 2.96/1.43  #Ref     : 0
% 2.96/1.43  #Sup     : 205
% 2.96/1.43  #Fact    : 0
% 2.96/1.43  #Define  : 0
% 2.96/1.43  #Split   : 5
% 2.96/1.43  #Chain   : 0
% 2.96/1.43  #Close   : 0
% 2.96/1.43  
% 2.96/1.43  Ordering : KBO
% 2.96/1.43  
% 2.96/1.43  Simplification rules
% 2.96/1.43  ----------------------
% 2.96/1.43  #Subsume      : 7
% 2.96/1.43  #Demod        : 194
% 2.96/1.43  #Tautology    : 68
% 2.96/1.43  #SimpNegUnit  : 0
% 2.96/1.43  #BackRed      : 0
% 2.96/1.43  
% 2.96/1.43  #Partial instantiations: 0
% 2.96/1.43  #Strategies tried      : 1
% 2.96/1.43  
% 2.96/1.43  Timing (in seconds)
% 2.96/1.43  ----------------------
% 2.96/1.43  Preprocessing        : 0.28
% 2.96/1.43  Parsing              : 0.16
% 2.96/1.43  CNF conversion       : 0.02
% 2.96/1.43  Main loop            : 0.37
% 2.96/1.43  Inferencing          : 0.15
% 2.96/1.43  Reduction            : 0.11
% 2.96/1.43  Demodulation         : 0.08
% 2.96/1.43  BG Simplification    : 0.02
% 2.96/1.43  Subsumption          : 0.06
% 2.96/1.43  Abstraction          : 0.03
% 2.96/1.43  MUC search           : 0.00
% 2.96/1.43  Cooper               : 0.00
% 2.96/1.43  Total                : 0.68
% 2.96/1.43  Index Insertion      : 0.00
% 2.96/1.44  Index Deletion       : 0.00
% 2.96/1.44  Index Matching       : 0.00
% 2.96/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:03:57 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 163 expanded)
%              Number of leaves         :   23 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 450 expanded)
%              Number of equality atoms :   52 ( 183 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
            & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_77,axiom,(
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
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

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

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_32,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    ! [A_22] :
      ( k2_relat_1(k2_funct_1(A_22)) = k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_19] :
      ( k7_relat_1(A_19,k1_relat_1(A_19)) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_8,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1020,plain,(
    ! [B_77,C_78,A_79] :
      ( k2_relat_1(k5_relat_1(B_77,C_78)) = k2_relat_1(k5_relat_1(A_79,C_78))
      | k2_relat_1(B_77) != k2_relat_1(A_79)
      | ~ v1_relat_1(C_78)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_22] :
      ( k1_relat_1(k2_funct_1(A_22)) = k2_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_471,plain,(
    ! [C_51,B_52,A_53] :
      ( k1_relat_1(k5_relat_1(C_51,B_52)) = k1_relat_1(k5_relat_1(C_51,A_53))
      | k1_relat_1(B_52) != k1_relat_1(A_53)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_78,plain,(
    k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_489,plain,(
    ! [A_53] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_53)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_53) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_78])).

tff(c_529,plain,(
    ! [A_53] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_53)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_53) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_489])).

tff(c_617,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_620,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_617])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_620])).

tff(c_626,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_6,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k6_relat_1(k2_relat_1(A_16))) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_627,plain,(
    ! [A_58] :
      ( k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'),A_58)) != k2_relat_1('#skF_1')
      | k1_relat_1(A_58) != k1_relat_1('#skF_1')
      | ~ v1_relat_1(A_58) ) ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_639,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) != k1_relat_1('#skF_1')
    | ~ v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_627])).

tff(c_645,plain,
    ( k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_20,c_6,c_639])).

tff(c_646,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_645])).

tff(c_649,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_646])).

tff(c_653,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_649])).

tff(c_654,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_645])).

tff(c_755,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_654])).

tff(c_759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_755])).

tff(c_760,plain,(
    k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'),'#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1047,plain,(
    ! [B_77] :
      ( k2_relat_1(k5_relat_1(B_77,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != k2_relat_1(B_77)
      | ~ v1_relat_1('#skF_1')
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_760])).

tff(c_1094,plain,(
    ! [B_77] :
      ( k2_relat_1(k5_relat_1(B_77,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != k2_relat_1(B_77)
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1047])).

tff(c_1230,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1094])).

tff(c_1233,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_1230])).

tff(c_1237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_1233])).

tff(c_1272,plain,(
    ! [B_86] :
      ( k2_relat_1(k5_relat_1(B_86,'#skF_1')) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != k2_relat_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(splitRight,[status(thm)],[c_1094])).

tff(c_1284,plain,(
    ! [A_17] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_17)) != k2_relat_1('#skF_1')
      | k2_relat_1(k6_relat_1(A_17)) != k2_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1272])).

tff(c_1368,plain,(
    ! [A_89] :
      ( k2_relat_1(k7_relat_1('#skF_1',A_89)) != k2_relat_1('#skF_1')
      | k2_relat_1(k2_funct_1('#skF_1')) != A_89 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_20,c_8,c_1284])).

tff(c_1372,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1368])).

tff(c_1375,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1372])).

tff(c_1378,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1375])).

tff(c_1382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_1378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:26:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  %$ v2_funct_1 > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.32/1.58  
% 3.32/1.58  %Foreground sorts:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Background operators:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Foreground operators:
% 3.32/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.32/1.58  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.32/1.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.58  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.32/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.58  
% 3.32/1.60  tff(f_98, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 3.32/1.60  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 3.32/1.60  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 3.32/1.60  tff(f_77, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.32/1.60  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.32/1.60  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.32/1.60  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.32/1.60  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t199_relat_1)).
% 3.32/1.60  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k1_relat_1(A) = k1_relat_1(B)) => (k1_relat_1(k5_relat_1(C, A)) = k1_relat_1(k5_relat_1(C, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t198_relat_1)).
% 3.32/1.60  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.32/1.60  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.60  tff(c_32, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.60  tff(c_30, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.60  tff(c_24, plain, (![A_22]: (k2_relat_1(k2_funct_1(A_22))=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.60  tff(c_14, plain, (![A_19]: (k7_relat_1(A_19, k1_relat_1(A_19))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.32/1.60  tff(c_20, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.32/1.60  tff(c_8, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.60  tff(c_12, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.32/1.60  tff(c_18, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.32/1.60  tff(c_1020, plain, (![B_77, C_78, A_79]: (k2_relat_1(k5_relat_1(B_77, C_78))=k2_relat_1(k5_relat_1(A_79, C_78)) | k2_relat_1(B_77)!=k2_relat_1(A_79) | ~v1_relat_1(C_78) | ~v1_relat_1(B_77) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.32/1.60  tff(c_26, plain, (![A_22]: (k1_relat_1(k2_funct_1(A_22))=k2_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.60  tff(c_471, plain, (![C_51, B_52, A_53]: (k1_relat_1(k5_relat_1(C_51, B_52))=k1_relat_1(k5_relat_1(C_51, A_53)) | k1_relat_1(B_52)!=k1_relat_1(A_53) | ~v1_relat_1(C_51) | ~v1_relat_1(B_52) | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.60  tff(c_28, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.32/1.60  tff(c_78, plain, (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 3.32/1.60  tff(c_489, plain, (![A_53]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_53))!=k2_relat_1('#skF_1') | k1_relat_1(A_53)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(A_53))), inference(superposition, [status(thm), theory('equality')], [c_471, c_78])).
% 3.32/1.60  tff(c_529, plain, (![A_53]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_53))!=k2_relat_1('#skF_1') | k1_relat_1(A_53)!=k1_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_489])).
% 3.32/1.60  tff(c_617, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_529])).
% 3.32/1.60  tff(c_620, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_617])).
% 3.32/1.60  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_620])).
% 3.32/1.60  tff(c_626, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_529])).
% 3.32/1.60  tff(c_6, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.60  tff(c_10, plain, (![A_16]: (k5_relat_1(A_16, k6_relat_1(k2_relat_1(A_16)))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.32/1.60  tff(c_627, plain, (![A_58]: (k1_relat_1(k5_relat_1(k2_funct_1('#skF_1'), A_58))!=k2_relat_1('#skF_1') | k1_relat_1(A_58)!=k1_relat_1('#skF_1') | ~v1_relat_1(A_58))), inference(splitRight, [status(thm)], [c_529])).
% 3.32/1.60  tff(c_639, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1'))))!=k1_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(k2_relat_1(k2_funct_1('#skF_1')))) | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_627])).
% 3.32/1.60  tff(c_645, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_626, c_20, c_6, c_639])).
% 3.32/1.60  tff(c_646, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_645])).
% 3.32/1.60  tff(c_649, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_646])).
% 3.32/1.60  tff(c_653, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_649])).
% 3.32/1.60  tff(c_654, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_645])).
% 3.32/1.60  tff(c_755, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_654])).
% 3.32/1.60  tff(c_759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_755])).
% 3.32/1.60  tff(c_760, plain, (k2_relat_1(k5_relat_1(k2_funct_1('#skF_1'), '#skF_1'))!=k2_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 3.32/1.60  tff(c_1047, plain, (![B_77]: (k2_relat_1(k5_relat_1(B_77, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1(B_77) | ~v1_relat_1('#skF_1') | ~v1_relat_1(B_77) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1020, c_760])).
% 3.32/1.60  tff(c_1094, plain, (![B_77]: (k2_relat_1(k5_relat_1(B_77, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1(B_77) | ~v1_relat_1(B_77) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1047])).
% 3.32/1.60  tff(c_1230, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1094])).
% 3.32/1.60  tff(c_1233, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1230])).
% 3.32/1.60  tff(c_1237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_1233])).
% 3.32/1.60  tff(c_1272, plain, (![B_86]: (k2_relat_1(k5_relat_1(B_86, '#skF_1'))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1(B_86) | ~v1_relat_1(B_86))), inference(splitRight, [status(thm)], [c_1094])).
% 3.32/1.60  tff(c_1284, plain, (![A_17]: (k2_relat_1(k7_relat_1('#skF_1', A_17))!=k2_relat_1('#skF_1') | k2_relat_1(k6_relat_1(A_17))!=k2_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1272])).
% 3.32/1.60  tff(c_1368, plain, (![A_89]: (k2_relat_1(k7_relat_1('#skF_1', A_89))!=k2_relat_1('#skF_1') | k2_relat_1(k2_funct_1('#skF_1'))!=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_20, c_8, c_1284])).
% 3.32/1.60  tff(c_1372, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_1368])).
% 3.32/1.60  tff(c_1375, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1372])).
% 3.32/1.60  tff(c_1378, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_24, c_1375])).
% 3.32/1.60  tff(c_1382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_1378])).
% 3.32/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.60  
% 3.32/1.60  Inference rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Ref     : 1
% 3.32/1.60  #Sup     : 305
% 3.32/1.60  #Fact    : 0
% 3.32/1.60  #Define  : 0
% 3.32/1.60  #Split   : 5
% 3.32/1.60  #Chain   : 0
% 3.32/1.60  #Close   : 0
% 3.32/1.60  
% 3.32/1.60  Ordering : KBO
% 3.32/1.60  
% 3.32/1.60  Simplification rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Subsume      : 11
% 3.32/1.60  #Demod        : 280
% 3.32/1.60  #Tautology    : 102
% 3.32/1.60  #SimpNegUnit  : 0
% 3.32/1.60  #BackRed      : 0
% 3.32/1.60  
% 3.32/1.60  #Partial instantiations: 0
% 3.32/1.60  #Strategies tried      : 1
% 3.32/1.60  
% 3.32/1.60  Timing (in seconds)
% 3.32/1.60  ----------------------
% 3.32/1.60  Preprocessing        : 0.29
% 3.32/1.60  Parsing              : 0.17
% 3.32/1.60  CNF conversion       : 0.02
% 3.32/1.60  Main loop            : 0.50
% 3.32/1.60  Inferencing          : 0.20
% 3.32/1.60  Reduction            : 0.16
% 3.32/1.60  Demodulation         : 0.12
% 3.32/1.60  BG Simplification    : 0.03
% 3.32/1.60  Subsumption          : 0.08
% 3.32/1.60  Abstraction          : 0.03
% 3.32/1.60  MUC search           : 0.00
% 3.32/1.60  Cooper               : 0.00
% 3.32/1.60  Total                : 0.83
% 3.32/1.60  Index Insertion      : 0.00
% 3.32/1.60  Index Deletion       : 0.00
% 3.32/1.60  Index Matching       : 0.00
% 3.32/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------

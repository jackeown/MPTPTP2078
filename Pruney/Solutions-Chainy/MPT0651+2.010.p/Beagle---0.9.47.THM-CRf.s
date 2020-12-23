%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:49 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 194 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  135 ( 550 expanded)
%              Number of equality atoms :   48 ( 228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
         => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
            & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( k2_relat_1(A) = k2_relat_1(B)
               => k2_relat_1(k5_relat_1(A,C)) = k2_relat_1(k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t199_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    v2_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    ! [A_21] :
      ( k2_relat_1(k2_funct_1(A_21)) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    ! [A_21] :
      ( k1_relat_1(k2_funct_1(A_21)) = k2_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1225,plain,(
    ! [B_102,C_103,A_104] :
      ( k2_relat_1(k5_relat_1(B_102,C_103)) = k2_relat_1(k5_relat_1(A_104,C_103))
      | k2_relat_1(B_102) != k2_relat_1(A_104)
      | ~ v1_relat_1(C_103)
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_39,B_40] :
      ( k1_relat_1(k5_relat_1(A_39,B_40)) = k1_relat_1(A_39)
      | ~ r1_tarski(k2_relat_1(A_39),k1_relat_1(B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_901,plain,(
    ! [A_78,A_79] :
      ( k1_relat_1(k5_relat_1(A_78,k2_funct_1(A_79))) = k1_relat_1(A_78)
      | ~ r1_tarski(k2_relat_1(A_78),k2_relat_1(A_79))
      | ~ v1_relat_1(k2_funct_1(A_79))
      | ~ v1_relat_1(A_78)
      | ~ v2_funct_1(A_79)
      | ~ v1_funct_1(A_79)
      | ~ v1_relat_1(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_135])).

tff(c_978,plain,(
    ! [A_80] :
      ( k1_relat_1(k5_relat_1(A_80,k2_funct_1(A_80))) = k1_relat_1(A_80)
      | ~ v1_relat_1(k2_funct_1(A_80))
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_901])).

tff(c_34,plain,
    ( k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
    | k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_64,plain,(
    k1_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_1000,plain,
    ( ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_64])).

tff(c_1017,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1000])).

tff(c_1025,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1017])).

tff(c_1029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1025])).

tff(c_1030,plain,(
    k2_relat_1(k5_relat_1('#skF_1',k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1246,plain,(
    ! [B_102] :
      ( k2_relat_1(k5_relat_1(B_102,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(B_102) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_1030])).

tff(c_1269,plain,(
    ! [B_102] :
      ( k2_relat_1(k5_relat_1(B_102,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(B_102) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k2_funct_1('#skF_1'))
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1246])).

tff(c_1433,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1269])).

tff(c_1436,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1433])).

tff(c_1440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1436])).

tff(c_1442,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1269])).

tff(c_8,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    ! [A_20] : v1_relat_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1443,plain,(
    ! [B_111] :
      ( k2_relat_1(k5_relat_1(B_111,k2_funct_1('#skF_1'))) != k1_relat_1('#skF_1')
      | k2_relat_1(B_111) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(B_111) ) ),
    inference(splitRight,[status(thm)],[c_1269])).

tff(c_1459,plain,(
    ! [A_17] :
      ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'),A_17)) != k1_relat_1('#skF_1')
      | k2_relat_1(k6_relat_1(A_17)) != k2_relat_1('#skF_1')
      | ~ v1_relat_1(k6_relat_1(A_17))
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1443])).

tff(c_1469,plain,(
    ! [A_112] :
      ( k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'),A_112)) != k1_relat_1('#skF_1')
      | k2_relat_1('#skF_1') != A_112 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_26,c_18,c_1459])).

tff(c_1477,plain,(
    ! [A_4] :
      ( k9_relat_1(k2_funct_1('#skF_1'),A_4) != k1_relat_1('#skF_1')
      | k2_relat_1('#skF_1') != A_4
      | ~ v1_relat_1(k2_funct_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_1469])).

tff(c_1483,plain,(
    ! [A_113] :
      ( k9_relat_1(k2_funct_1('#skF_1'),A_113) != k1_relat_1('#skF_1')
      | k2_relat_1('#skF_1') != A_113 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_1477])).

tff(c_1487,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1483])).

tff(c_1489,plain,
    ( k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1')
    | k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1442,c_1487])).

tff(c_1490,plain,(
    k1_relat_1(k2_funct_1('#skF_1')) != k2_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1489])).

tff(c_1495,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_1490])).

tff(c_1499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1495])).

tff(c_1500,plain,(
    k2_relat_1(k2_funct_1('#skF_1')) != k1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1489])).

tff(c_1504,plain,
    ( ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1500])).

tff(c_1508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:12:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.49/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.55  
% 3.49/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.55  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_relat_1 > #skF_1
% 3.49/1.55  
% 3.49/1.55  %Foreground sorts:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Background operators:
% 3.49/1.55  
% 3.49/1.55  
% 3.49/1.55  %Foreground operators:
% 3.49/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.49/1.55  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.49/1.55  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.49/1.55  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.49/1.55  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.49/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.49/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.49/1.55  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.49/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.49/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.49/1.55  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.49/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.49/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.49/1.55  
% 3.49/1.56  tff(f_101, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 3.49/1.56  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 3.49/1.56  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 3.49/1.56  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((k2_relat_1(A) = k2_relat_1(B)) => (k2_relat_1(k5_relat_1(A, C)) = k2_relat_1(k5_relat_1(B, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t199_relat_1)).
% 3.49/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.49/1.56  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 3.49/1.56  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.49/1.56  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.49/1.56  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 3.49/1.56  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.49/1.56  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.49/1.56  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.49/1.56  tff(c_38, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.49/1.56  tff(c_36, plain, (v2_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.49/1.56  tff(c_30, plain, (![A_21]: (k2_relat_1(k2_funct_1(A_21))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.49/1.56  tff(c_32, plain, (![A_21]: (k1_relat_1(k2_funct_1(A_21))=k2_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.49/1.56  tff(c_24, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.49/1.56  tff(c_1225, plain, (![B_102, C_103, A_104]: (k2_relat_1(k5_relat_1(B_102, C_103))=k2_relat_1(k5_relat_1(A_104, C_103)) | k2_relat_1(B_102)!=k2_relat_1(A_104) | ~v1_relat_1(C_103) | ~v1_relat_1(B_102) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.49/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.49/1.56  tff(c_135, plain, (![A_39, B_40]: (k1_relat_1(k5_relat_1(A_39, B_40))=k1_relat_1(A_39) | ~r1_tarski(k2_relat_1(A_39), k1_relat_1(B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.49/1.56  tff(c_901, plain, (![A_78, A_79]: (k1_relat_1(k5_relat_1(A_78, k2_funct_1(A_79)))=k1_relat_1(A_78) | ~r1_tarski(k2_relat_1(A_78), k2_relat_1(A_79)) | ~v1_relat_1(k2_funct_1(A_79)) | ~v1_relat_1(A_78) | ~v2_funct_1(A_79) | ~v1_funct_1(A_79) | ~v1_relat_1(A_79))), inference(superposition, [status(thm), theory('equality')], [c_32, c_135])).
% 3.49/1.56  tff(c_978, plain, (![A_80]: (k1_relat_1(k5_relat_1(A_80, k2_funct_1(A_80)))=k1_relat_1(A_80) | ~v1_relat_1(k2_funct_1(A_80)) | ~v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_6, c_901])).
% 3.49/1.56  tff(c_34, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.49/1.56  tff(c_64, plain, (k1_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_34])).
% 3.49/1.56  tff(c_1000, plain, (~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_978, c_64])).
% 3.49/1.56  tff(c_1017, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1000])).
% 3.49/1.56  tff(c_1025, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1017])).
% 3.49/1.56  tff(c_1029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1025])).
% 3.49/1.56  tff(c_1030, plain, (k2_relat_1(k5_relat_1('#skF_1', k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_34])).
% 3.49/1.56  tff(c_1246, plain, (![B_102]: (k2_relat_1(k5_relat_1(B_102, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(B_102)!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_102) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1225, c_1030])).
% 3.49/1.56  tff(c_1269, plain, (![B_102]: (k2_relat_1(k5_relat_1(B_102, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(B_102)!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1246])).
% 3.49/1.56  tff(c_1433, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1269])).
% 3.49/1.56  tff(c_1436, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1433])).
% 3.49/1.56  tff(c_1440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1436])).
% 3.49/1.56  tff(c_1442, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1269])).
% 3.49/1.56  tff(c_8, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.49/1.56  tff(c_10, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.49/1.56  tff(c_26, plain, (![A_20]: (v1_relat_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.49/1.56  tff(c_18, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.49/1.56  tff(c_20, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.49/1.56  tff(c_1443, plain, (![B_111]: (k2_relat_1(k5_relat_1(B_111, k2_funct_1('#skF_1')))!=k1_relat_1('#skF_1') | k2_relat_1(B_111)!=k2_relat_1('#skF_1') | ~v1_relat_1(B_111))), inference(splitRight, [status(thm)], [c_1269])).
% 3.49/1.56  tff(c_1459, plain, (![A_17]: (k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'), A_17))!=k1_relat_1('#skF_1') | k2_relat_1(k6_relat_1(A_17))!=k2_relat_1('#skF_1') | ~v1_relat_1(k6_relat_1(A_17)) | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1443])).
% 3.49/1.56  tff(c_1469, plain, (![A_112]: (k2_relat_1(k7_relat_1(k2_funct_1('#skF_1'), A_112))!=k1_relat_1('#skF_1') | k2_relat_1('#skF_1')!=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_26, c_18, c_1459])).
% 3.49/1.56  tff(c_1477, plain, (![A_4]: (k9_relat_1(k2_funct_1('#skF_1'), A_4)!=k1_relat_1('#skF_1') | k2_relat_1('#skF_1')!=A_4 | ~v1_relat_1(k2_funct_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10, c_1469])).
% 3.49/1.56  tff(c_1483, plain, (![A_113]: (k9_relat_1(k2_funct_1('#skF_1'), A_113)!=k1_relat_1('#skF_1') | k2_relat_1('#skF_1')!=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_1477])).
% 3.49/1.56  tff(c_1487, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_1483])).
% 3.49/1.56  tff(c_1489, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1') | k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1442, c_1487])).
% 3.49/1.56  tff(c_1490, plain, (k1_relat_1(k2_funct_1('#skF_1'))!=k2_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_1489])).
% 3.49/1.56  tff(c_1495, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_32, c_1490])).
% 3.49/1.56  tff(c_1499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1495])).
% 3.49/1.56  tff(c_1500, plain, (k2_relat_1(k2_funct_1('#skF_1'))!=k1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_1489])).
% 3.49/1.56  tff(c_1504, plain, (~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_30, c_1500])).
% 3.49/1.56  tff(c_1508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1504])).
% 3.49/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/1.56  
% 3.49/1.56  Inference rules
% 3.49/1.56  ----------------------
% 3.49/1.56  #Ref     : 2
% 3.49/1.56  #Sup     : 361
% 3.49/1.56  #Fact    : 0
% 3.49/1.56  #Define  : 0
% 3.49/1.56  #Split   : 4
% 3.49/1.56  #Chain   : 0
% 3.49/1.57  #Close   : 0
% 3.49/1.57  
% 3.49/1.57  Ordering : KBO
% 3.49/1.57  
% 3.49/1.57  Simplification rules
% 3.49/1.57  ----------------------
% 3.49/1.57  #Subsume      : 18
% 3.49/1.57  #Demod        : 185
% 3.49/1.57  #Tautology    : 101
% 3.49/1.57  #SimpNegUnit  : 0
% 3.49/1.57  #BackRed      : 0
% 3.49/1.57  
% 3.49/1.57  #Partial instantiations: 0
% 3.49/1.57  #Strategies tried      : 1
% 3.49/1.57  
% 3.49/1.57  Timing (in seconds)
% 3.49/1.57  ----------------------
% 3.49/1.57  Preprocessing        : 0.30
% 3.49/1.57  Parsing              : 0.16
% 3.49/1.57  CNF conversion       : 0.02
% 3.49/1.57  Main loop            : 0.51
% 3.49/1.57  Inferencing          : 0.19
% 3.49/1.57  Reduction            : 0.16
% 3.49/1.57  Demodulation         : 0.12
% 3.49/1.57  BG Simplification    : 0.03
% 3.49/1.57  Subsumption          : 0.10
% 3.49/1.57  Abstraction          : 0.03
% 3.49/1.57  MUC search           : 0.00
% 3.49/1.57  Cooper               : 0.00
% 3.49/1.57  Total                : 0.84
% 3.49/1.57  Index Insertion      : 0.00
% 3.49/1.57  Index Deletion       : 0.00
% 3.49/1.57  Index Matching       : 0.00
% 3.49/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

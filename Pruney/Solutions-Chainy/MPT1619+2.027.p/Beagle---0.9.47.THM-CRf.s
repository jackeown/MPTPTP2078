%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:43 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   42 (  48 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  69 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_funcop_1,type,(
    k2_funcop_1: ( $i * $i ) > $i )).

tff(k7_funcop_1,type,(
    k7_funcop_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_yellow_1,type,(
    k5_yellow_1: ( $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_yellow_1,type,(
    k6_yellow_1: ( $i * $i ) > $i )).

tff(g1_orders_2,type,(
    g1_orders_2: ( $i * $i ) > $i )).

tff(v1_yellow_1,type,(
    v1_yellow_1: $i > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( l1_orders_2(A)
       => k6_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_1)).

tff(f_43,axiom,(
    ! [A,B] : k7_funcop_1(A,B) = k2_funcop_1(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_funcop_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => k6_yellow_1(A,B) = k5_yellow_1(A,k7_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( l1_orders_2(B)
     => v1_yellow_1(k2_funcop_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_yellow_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(k2_funcop_1(A,B))
      & v4_relat_1(k2_funcop_1(A,B),A)
      & v1_funct_1(k2_funcop_1(A,B))
      & v1_partfun1(k2_funcop_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc20_funcop_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v4_relat_1(A,k1_xboole_0)
        & v1_funct_1(A)
        & v1_partfun1(A,k1_xboole_0)
        & v1_yellow_1(A) )
     => k5_yellow_1(k1_xboole_0,A) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_1)).

tff(c_20,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_7,B_8] : k7_funcop_1(A_7,B_8) = k2_funcop_1(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k5_yellow_1(A_1,k7_funcop_1(A_1,B_2)) = k6_yellow_1(A_1,B_2)
      | ~ l1_orders_2(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_21,plain,(
    ! [A_1,B_2] :
      ( k5_yellow_1(A_1,k2_funcop_1(A_1,B_2)) = k6_yellow_1(A_1,B_2)
      | ~ l1_orders_2(B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_yellow_1(k2_funcop_1(A_3,B_4))
      | ~ l1_orders_2(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_funcop_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_5,B_6] : v1_funct_1(k2_funcop_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_5,B_6] : v1_partfun1(k2_funcop_1(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5,B_6] : v4_relat_1(k2_funcop_1(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [A_24] :
      ( k5_yellow_1(k1_xboole_0,A_24) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(A_24)
      | ~ v1_partfun1(A_24,k1_xboole_0)
      | ~ v1_funct_1(A_24)
      | ~ v4_relat_1(A_24,k1_xboole_0)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [B_6] :
      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,B_6)) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,B_6))
      | ~ v1_partfun1(k2_funcop_1(k1_xboole_0,B_6),k1_xboole_0)
      | ~ v1_funct_1(k2_funcop_1(k1_xboole_0,B_6))
      | ~ v1_relat_1(k2_funcop_1(k1_xboole_0,B_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_45])).

tff(c_52,plain,(
    ! [B_25] :
      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,B_25)) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ v1_yellow_1(k2_funcop_1(k1_xboole_0,B_25)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_12,c_48])).

tff(c_57,plain,(
    ! [B_26] :
      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,B_26)) = g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(B_26) ) ),
    inference(resolution,[status(thm)],[c_4,c_52])).

tff(c_18,plain,(
    g1_orders_2(k1_tarski(k1_xboole_0),k6_partfun1(k1_tarski(k1_xboole_0))) != k6_yellow_1(k1_xboole_0,'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    ! [B_27] :
      ( k5_yellow_1(k1_xboole_0,k2_funcop_1(k1_xboole_0,B_27)) != k6_yellow_1(k1_xboole_0,'#skF_1')
      | ~ l1_orders_2(B_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_18])).

tff(c_84,plain,(
    ! [B_28] :
      ( k6_yellow_1(k1_xboole_0,B_28) != k6_yellow_1(k1_xboole_0,'#skF_1')
      | ~ l1_orders_2(B_28)
      | ~ l1_orders_2(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21,c_76])).

tff(c_86,plain,(
    ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_84])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:33:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.10  
% 1.67/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.10  %$ v4_relat_1 > v1_partfun1 > v1_yellow_1 > v1_relat_1 > v1_funct_1 > l1_orders_2 > k7_funcop_1 > k6_yellow_1 > k5_yellow_1 > k2_funcop_1 > g1_orders_2 > #nlpp > k6_partfun1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.67/1.10  
% 1.67/1.10  %Foreground sorts:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Background operators:
% 1.67/1.10  
% 1.67/1.10  
% 1.67/1.10  %Foreground operators:
% 1.67/1.10  tff(k2_funcop_1, type, k2_funcop_1: ($i * $i) > $i).
% 1.67/1.10  tff(k7_funcop_1, type, k7_funcop_1: ($i * $i) > $i).
% 1.67/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.10  tff(k5_yellow_1, type, k5_yellow_1: ($i * $i) > $i).
% 1.67/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.10  tff(k6_yellow_1, type, k6_yellow_1: ($i * $i) > $i).
% 1.67/1.10  tff(g1_orders_2, type, g1_orders_2: ($i * $i) > $i).
% 1.67/1.10  tff(v1_yellow_1, type, v1_yellow_1: $i > $o).
% 1.67/1.10  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 1.67/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.10  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.67/1.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.67/1.10  
% 1.67/1.11  tff(f_60, negated_conjecture, ~(![A]: (l1_orders_2(A) => (k6_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_1)).
% 1.67/1.11  tff(f_43, axiom, (![A, B]: (k7_funcop_1(A, B) = k2_funcop_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_funcop_1)).
% 1.67/1.11  tff(f_29, axiom, (![A, B]: (l1_orders_2(B) => (k6_yellow_1(A, B) = k5_yellow_1(A, k7_funcop_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_1)).
% 1.67/1.11  tff(f_33, axiom, (![A, B]: (l1_orders_2(B) => v1_yellow_1(k2_funcop_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_yellow_1)).
% 1.67/1.11  tff(f_41, axiom, (![A, B]: (((v1_relat_1(k2_funcop_1(A, B)) & v4_relat_1(k2_funcop_1(A, B), A)) & v1_funct_1(k2_funcop_1(A, B))) & v1_partfun1(k2_funcop_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc20_funcop_1)).
% 1.67/1.11  tff(f_55, axiom, (![A]: (((((v1_relat_1(A) & v4_relat_1(A, k1_xboole_0)) & v1_funct_1(A)) & v1_partfun1(A, k1_xboole_0)) & v1_yellow_1(A)) => (k5_yellow_1(k1_xboole_0, A) = g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_yellow_1)).
% 1.67/1.11  tff(c_20, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.67/1.11  tff(c_14, plain, (![A_7, B_8]: (k7_funcop_1(A_7, B_8)=k2_funcop_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.11  tff(c_2, plain, (![A_1, B_2]: (k5_yellow_1(A_1, k7_funcop_1(A_1, B_2))=k6_yellow_1(A_1, B_2) | ~l1_orders_2(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.11  tff(c_21, plain, (![A_1, B_2]: (k5_yellow_1(A_1, k2_funcop_1(A_1, B_2))=k6_yellow_1(A_1, B_2) | ~l1_orders_2(B_2))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2])).
% 1.67/1.11  tff(c_4, plain, (![A_3, B_4]: (v1_yellow_1(k2_funcop_1(A_3, B_4)) | ~l1_orders_2(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.67/1.11  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k2_funcop_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.11  tff(c_10, plain, (![A_5, B_6]: (v1_funct_1(k2_funcop_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.11  tff(c_12, plain, (![A_5, B_6]: (v1_partfun1(k2_funcop_1(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.11  tff(c_8, plain, (![A_5, B_6]: (v4_relat_1(k2_funcop_1(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.11  tff(c_45, plain, (![A_24]: (k5_yellow_1(k1_xboole_0, A_24)=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(A_24) | ~v1_partfun1(A_24, k1_xboole_0) | ~v1_funct_1(A_24) | ~v4_relat_1(A_24, k1_xboole_0) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.67/1.11  tff(c_48, plain, (![B_6]: (k5_yellow_1(k1_xboole_0, k2_funcop_1(k1_xboole_0, B_6))=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(k2_funcop_1(k1_xboole_0, B_6)) | ~v1_partfun1(k2_funcop_1(k1_xboole_0, B_6), k1_xboole_0) | ~v1_funct_1(k2_funcop_1(k1_xboole_0, B_6)) | ~v1_relat_1(k2_funcop_1(k1_xboole_0, B_6)))), inference(resolution, [status(thm)], [c_8, c_45])).
% 1.67/1.11  tff(c_52, plain, (![B_25]: (k5_yellow_1(k1_xboole_0, k2_funcop_1(k1_xboole_0, B_25))=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~v1_yellow_1(k2_funcop_1(k1_xboole_0, B_25)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_12, c_48])).
% 1.67/1.11  tff(c_57, plain, (![B_26]: (k5_yellow_1(k1_xboole_0, k2_funcop_1(k1_xboole_0, B_26))=g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0))) | ~l1_orders_2(B_26))), inference(resolution, [status(thm)], [c_4, c_52])).
% 1.67/1.11  tff(c_18, plain, (g1_orders_2(k1_tarski(k1_xboole_0), k6_partfun1(k1_tarski(k1_xboole_0)))!=k6_yellow_1(k1_xboole_0, '#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.67/1.11  tff(c_76, plain, (![B_27]: (k5_yellow_1(k1_xboole_0, k2_funcop_1(k1_xboole_0, B_27))!=k6_yellow_1(k1_xboole_0, '#skF_1') | ~l1_orders_2(B_27))), inference(superposition, [status(thm), theory('equality')], [c_57, c_18])).
% 1.67/1.11  tff(c_84, plain, (![B_28]: (k6_yellow_1(k1_xboole_0, B_28)!=k6_yellow_1(k1_xboole_0, '#skF_1') | ~l1_orders_2(B_28) | ~l1_orders_2(B_28))), inference(superposition, [status(thm), theory('equality')], [c_21, c_76])).
% 1.67/1.11  tff(c_86, plain, (~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_20, c_84])).
% 1.67/1.11  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_86])).
% 1.67/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.67/1.11  
% 1.67/1.11  Inference rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Ref     : 0
% 1.67/1.11  #Sup     : 16
% 1.67/1.11  #Fact    : 0
% 1.67/1.11  #Define  : 0
% 1.67/1.11  #Split   : 0
% 1.67/1.11  #Chain   : 0
% 1.67/1.11  #Close   : 0
% 1.67/1.11  
% 1.67/1.11  Ordering : KBO
% 1.67/1.11  
% 1.67/1.11  Simplification rules
% 1.67/1.11  ----------------------
% 1.67/1.11  #Subsume      : 1
% 1.67/1.11  #Demod        : 5
% 1.67/1.11  #Tautology    : 6
% 1.67/1.11  #SimpNegUnit  : 0
% 1.67/1.11  #BackRed      : 0
% 1.67/1.11  
% 1.67/1.11  #Partial instantiations: 0
% 1.67/1.11  #Strategies tried      : 1
% 1.67/1.11  
% 1.67/1.11  Timing (in seconds)
% 1.67/1.11  ----------------------
% 1.67/1.12  Preprocessing        : 0.28
% 1.67/1.12  Parsing              : 0.15
% 1.67/1.12  CNF conversion       : 0.01
% 1.67/1.12  Main loop            : 0.10
% 1.67/1.12  Inferencing          : 0.04
% 1.67/1.12  Reduction            : 0.03
% 1.67/1.12  Demodulation         : 0.02
% 1.67/1.12  BG Simplification    : 0.01
% 1.67/1.12  Subsumption          : 0.01
% 1.67/1.12  Abstraction          : 0.01
% 1.67/1.12  MUC search           : 0.00
% 1.67/1.12  Cooper               : 0.00
% 1.67/1.12  Total                : 0.40
% 1.67/1.12  Index Insertion      : 0.00
% 1.67/1.12  Index Deletion       : 0.00
% 1.67/1.12  Index Matching       : 0.00
% 1.67/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

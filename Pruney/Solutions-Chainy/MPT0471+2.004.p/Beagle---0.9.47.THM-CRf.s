%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:21 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 111 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 132 expanded)
%              Number of equality atoms :   20 (  43 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

tff(f_55,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_71,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(c_40,plain,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k2_xboole_0(A_48,B_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_120])).

tff(c_167,plain,(
    ! [A_52,B_53] : r1_xboole_0(k4_xboole_0(A_52,B_53),k4_xboole_0(B_53,A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_170,plain,(
    ! [A_11] : r1_xboole_0(k1_xboole_0,k4_xboole_0(A_11,A_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_167])).

tff(c_180,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_170])).

tff(c_295,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,B_75)
      | ~ r2_hidden(C_76,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_315,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_180,c_295])).

tff(c_30,plain,(
    ! [A_29] : v1_xboole_0(k1_subset_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_48,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_52,plain,(
    ! [A_29] : k1_subset_1(A_29) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_42,plain,(
    ! [A_37] :
      ( v1_relat_1(A_37)
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [A_29] : v1_relat_1(k1_subset_1(A_29)) ),
    inference(resolution,[status(thm)],[c_30,c_42])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46])).

tff(c_63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_30])).

tff(c_81,plain,(
    ! [A_42] :
      ( v1_xboole_0(k1_relat_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [A_46] :
      ( k1_relat_1(A_46) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_81,c_6])).

tff(c_100,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_63,c_92])).

tff(c_580,plain,(
    ! [A_90,B_91] :
      ( r2_hidden('#skF_3'(A_90,B_91),k1_relat_1(B_91))
      | ~ r2_hidden(A_90,k2_relat_1(B_91))
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_589,plain,(
    ! [A_90] :
      ( r2_hidden('#skF_3'(A_90,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_90,k2_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_580])).

tff(c_593,plain,(
    ! [A_90] :
      ( r2_hidden('#skF_3'(A_90,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_90,k2_relat_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_589])).

tff(c_595,plain,(
    ! [A_92] : ~ r2_hidden(A_92,k2_relat_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_315,c_593])).

tff(c_610,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_4,c_595])).

tff(c_621,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_610,c_6])).

tff(c_347,plain,(
    ! [A_80] :
      ( k2_xboole_0(k1_relat_1(A_80),k2_relat_1(A_80)) = k3_relat_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_362,plain,
    ( k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_347])).

tff(c_366,plain,(
    k2_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k3_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_362])).

tff(c_625,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k3_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_366])).

tff(c_627,plain,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_625])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_627])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:57:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.33  
% 2.67/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.33  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k5_enumset1 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.67/1.33  
% 2.67/1.33  %Foreground sorts:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Background operators:
% 2.67/1.33  
% 2.67/1.33  
% 2.67/1.33  %Foreground operators:
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.33  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.67/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.67/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.67/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.67/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.33  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.67/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.67/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.67/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.33  
% 2.67/1.35  tff(f_94, negated_conjecture, ~(k3_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_relat_1)).
% 2.67/1.35  tff(f_55, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.67/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.67/1.35  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.67/1.35  tff(f_61, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_xboole_1)).
% 2.67/1.35  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.67/1.35  tff(f_71, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 2.67/1.35  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.67/1.35  tff(f_75, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.67/1.35  tff(f_83, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.67/1.35  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 2.67/1.35  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.67/1.35  tff(c_40, plain, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.67/1.35  tff(c_14, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.35  tff(c_120, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k2_xboole_0(A_48, B_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.67/1.35  tff(c_127, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_120])).
% 2.67/1.35  tff(c_167, plain, (![A_52, B_53]: (r1_xboole_0(k4_xboole_0(A_52, B_53), k4_xboole_0(B_53, A_52)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.67/1.35  tff(c_170, plain, (![A_11]: (r1_xboole_0(k1_xboole_0, k4_xboole_0(A_11, A_11)))), inference(superposition, [status(thm), theory('equality')], [c_127, c_167])).
% 2.67/1.35  tff(c_180, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_170])).
% 2.67/1.35  tff(c_295, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, B_75) | ~r2_hidden(C_76, A_74))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.35  tff(c_315, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(resolution, [status(thm)], [c_180, c_295])).
% 2.67/1.35  tff(c_30, plain, (![A_29]: (v1_xboole_0(k1_subset_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.67/1.35  tff(c_48, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.35  tff(c_52, plain, (![A_29]: (k1_subset_1(A_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_48])).
% 2.67/1.35  tff(c_42, plain, (![A_37]: (v1_relat_1(A_37) | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.67/1.35  tff(c_46, plain, (![A_29]: (v1_relat_1(k1_subset_1(A_29)))), inference(resolution, [status(thm)], [c_30, c_42])).
% 2.67/1.35  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46])).
% 2.67/1.35  tff(c_63, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_30])).
% 2.67/1.35  tff(c_81, plain, (![A_42]: (v1_xboole_0(k1_relat_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.67/1.35  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.35  tff(c_92, plain, (![A_46]: (k1_relat_1(A_46)=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_81, c_6])).
% 2.67/1.35  tff(c_100, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_63, c_92])).
% 2.67/1.35  tff(c_580, plain, (![A_90, B_91]: (r2_hidden('#skF_3'(A_90, B_91), k1_relat_1(B_91)) | ~r2_hidden(A_90, k2_relat_1(B_91)) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.67/1.35  tff(c_589, plain, (![A_90]: (r2_hidden('#skF_3'(A_90, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_90, k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_100, c_580])).
% 2.67/1.35  tff(c_593, plain, (![A_90]: (r2_hidden('#skF_3'(A_90, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_90, k2_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_589])).
% 2.67/1.35  tff(c_595, plain, (![A_92]: (~r2_hidden(A_92, k2_relat_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_315, c_593])).
% 2.67/1.35  tff(c_610, plain, (v1_xboole_0(k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_595])).
% 2.67/1.35  tff(c_621, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_610, c_6])).
% 2.67/1.35  tff(c_347, plain, (![A_80]: (k2_xboole_0(k1_relat_1(A_80), k2_relat_1(A_80))=k3_relat_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.67/1.35  tff(c_362, plain, (k2_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))=k3_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_347])).
% 2.67/1.35  tff(c_366, plain, (k2_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))=k3_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_362])).
% 2.67/1.35  tff(c_625, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k3_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_621, c_366])).
% 2.67/1.35  tff(c_627, plain, (k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_625])).
% 2.67/1.35  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_627])).
% 2.67/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.35  
% 2.67/1.35  Inference rules
% 2.67/1.35  ----------------------
% 2.67/1.35  #Ref     : 0
% 2.67/1.35  #Sup     : 142
% 2.67/1.35  #Fact    : 0
% 2.67/1.35  #Define  : 0
% 2.67/1.35  #Split   : 0
% 2.67/1.35  #Chain   : 0
% 2.67/1.35  #Close   : 0
% 2.67/1.35  
% 2.67/1.35  Ordering : KBO
% 2.67/1.35  
% 2.67/1.35  Simplification rules
% 2.67/1.35  ----------------------
% 2.67/1.35  #Subsume      : 5
% 2.67/1.35  #Demod        : 62
% 2.67/1.35  #Tautology    : 88
% 2.67/1.35  #SimpNegUnit  : 3
% 2.67/1.35  #BackRed      : 7
% 2.67/1.35  
% 2.67/1.35  #Partial instantiations: 0
% 2.67/1.35  #Strategies tried      : 1
% 2.67/1.35  
% 2.67/1.35  Timing (in seconds)
% 2.67/1.35  ----------------------
% 2.67/1.35  Preprocessing        : 0.32
% 2.67/1.35  Parsing              : 0.18
% 2.67/1.35  CNF conversion       : 0.02
% 2.67/1.35  Main loop            : 0.26
% 2.67/1.35  Inferencing          : 0.10
% 2.67/1.35  Reduction            : 0.09
% 2.67/1.35  Demodulation         : 0.06
% 2.67/1.35  BG Simplification    : 0.01
% 2.67/1.35  Subsumption          : 0.04
% 2.67/1.35  Abstraction          : 0.02
% 2.67/1.35  MUC search           : 0.00
% 2.67/1.35  Cooper               : 0.00
% 2.67/1.35  Total                : 0.61
% 2.67/1.35  Index Insertion      : 0.00
% 2.67/1.35  Index Deletion       : 0.00
% 2.67/1.35  Index Matching       : 0.00
% 2.67/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

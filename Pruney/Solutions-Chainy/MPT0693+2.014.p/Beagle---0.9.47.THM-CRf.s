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
% DateTime   : Thu Dec  3 10:04:53 EST 2020

% Result     : Theorem 8.22s
% Output     : CNFRefutation 8.58s
% Verified   : 
% Statistics : Number of formulae       :   62 (  86 expanded)
%              Number of leaves         :   32 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :   84 ( 126 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_81,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_38,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_35] : v1_relat_1(k6_relat_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_33] : k1_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [B_39,A_38] : k5_relat_1(k6_relat_1(B_39),k6_relat_1(A_38)) = k6_relat_1(k3_xboole_0(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_246,plain,(
    ! [A_67,B_68] :
      ( k10_relat_1(A_67,k1_relat_1(B_68)) = k1_relat_1(k5_relat_1(A_67,B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_262,plain,(
    ! [A_67,A_33] :
      ( k1_relat_1(k5_relat_1(A_67,k6_relat_1(A_33))) = k10_relat_1(A_67,A_33)
      | ~ v1_relat_1(k6_relat_1(A_33))
      | ~ v1_relat_1(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_246])).

tff(c_293,plain,(
    ! [A_74,A_75] :
      ( k1_relat_1(k5_relat_1(A_74,k6_relat_1(A_75))) = k10_relat_1(A_74,A_75)
      | ~ v1_relat_1(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_262])).

tff(c_315,plain,(
    ! [A_38,B_39] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_38,B_39))) = k10_relat_1(k6_relat_1(B_39),A_38)
      | ~ v1_relat_1(k6_relat_1(B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_293])).

tff(c_327,plain,(
    ! [B_39,A_38] : k10_relat_1(k6_relat_1(B_39),A_38) = k3_xboole_0(A_38,B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_315])).

tff(c_26,plain,(
    ! [A_34] :
      ( k5_relat_1(A_34,k6_relat_1(k2_relat_1(A_34))) = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_583,plain,(
    ! [B_92,C_93,A_94] :
      ( k10_relat_1(k5_relat_1(B_92,C_93),A_94) = k10_relat_1(B_92,k10_relat_1(C_93,A_94))
      | ~ v1_relat_1(C_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_617,plain,(
    ! [A_34,A_94] :
      ( k10_relat_1(A_34,k10_relat_1(k6_relat_1(k2_relat_1(A_34)),A_94)) = k10_relat_1(A_34,A_94)
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(A_34)))
      | ~ v1_relat_1(A_34)
      | ~ v1_relat_1(A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_583])).

tff(c_625,plain,(
    ! [A_34,A_94] :
      ( k10_relat_1(A_34,k3_xboole_0(A_94,k2_relat_1(A_34))) = k10_relat_1(A_34,A_94)
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_327,c_617])).

tff(c_79,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(k10_relat_1(B_48,A_49),k1_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [A_33,A_49] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_33),A_49),A_33)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_79])).

tff(c_84,plain,(
    ! [A_33,A_49] : r1_tarski(k10_relat_1(k6_relat_1(A_33),A_49),A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_82])).

tff(c_253,plain,(
    ! [A_33,B_68] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_33),B_68)),A_33)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_84])).

tff(c_269,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_69),B_70)),A_69)
      | ~ v1_relat_1(B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_253])).

tff(c_272,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_38,B_39))),B_39)
      | ~ v1_relat_1(k6_relat_1(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_269])).

tff(c_281,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_272])).

tff(c_436,plain,(
    ! [B_85,A_86] :
      ( k9_relat_1(B_85,k10_relat_1(B_85,A_86)) = A_86
      | ~ r1_tarski(A_86,k2_relat_1(B_85))
      | ~ v1_funct_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2864,plain,(
    ! [B_173,A_174] :
      ( k9_relat_1(B_173,k10_relat_1(B_173,k3_xboole_0(A_174,k2_relat_1(B_173)))) = k3_xboole_0(A_174,k2_relat_1(B_173))
      | ~ v1_funct_1(B_173)
      | ~ v1_relat_1(B_173) ) ),
    inference(resolution,[status(thm)],[c_281,c_436])).

tff(c_13588,plain,(
    ! [A_373,A_374] :
      ( k9_relat_1(A_373,k10_relat_1(A_373,A_374)) = k3_xboole_0(A_374,k2_relat_1(A_373))
      | ~ v1_funct_1(A_373)
      | ~ v1_relat_1(A_373)
      | ~ v1_relat_1(A_373) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_2864])).

tff(c_109,plain,(
    ! [A_54] :
      ( k9_relat_1(A_54,k1_relat_1(A_54)) = k2_relat_1(A_54)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    k3_xboole_0('#skF_1',k9_relat_1('#skF_2',k1_relat_1('#skF_2'))) != k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_115,plain,
    ( k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_36])).

tff(c_124,plain,(
    k9_relat_1('#skF_2',k10_relat_1('#skF_2','#skF_1')) != k3_xboole_0('#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_115])).

tff(c_13602,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13588,c_124])).

tff(c_13645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_13602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:19:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.22/2.93  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/2.93  
% 8.22/2.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.22/2.94  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 8.22/2.94  
% 8.22/2.94  %Foreground sorts:
% 8.22/2.94  
% 8.22/2.94  
% 8.22/2.94  %Background operators:
% 8.22/2.94  
% 8.22/2.94  
% 8.22/2.94  %Foreground operators:
% 8.22/2.94  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.22/2.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.22/2.94  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.22/2.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.22/2.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.22/2.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.22/2.94  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.22/2.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.22/2.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.22/2.94  tff('#skF_2', type, '#skF_2': $i).
% 8.22/2.94  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.22/2.94  tff('#skF_1', type, '#skF_1': $i).
% 8.22/2.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.22/2.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.22/2.94  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 8.22/2.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.22/2.94  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.22/2.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.22/2.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.22/2.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.22/2.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.22/2.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.22/2.94  
% 8.58/2.95  tff(f_88, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 8.58/2.95  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 8.58/2.95  tff(f_63, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.58/2.95  tff(f_81, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 8.58/2.95  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 8.58/2.95  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 8.58/2.95  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 8.58/2.95  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 8.58/2.95  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 8.58/2.95  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 8.58/2.95  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.58/2.95  tff(c_38, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.58/2.95  tff(c_28, plain, (![A_35]: (v1_relat_1(k6_relat_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.58/2.95  tff(c_22, plain, (![A_33]: (k1_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.58/2.95  tff(c_34, plain, (![B_39, A_38]: (k5_relat_1(k6_relat_1(B_39), k6_relat_1(A_38))=k6_relat_1(k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.58/2.95  tff(c_246, plain, (![A_67, B_68]: (k10_relat_1(A_67, k1_relat_1(B_68))=k1_relat_1(k5_relat_1(A_67, B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.58/2.95  tff(c_262, plain, (![A_67, A_33]: (k1_relat_1(k5_relat_1(A_67, k6_relat_1(A_33)))=k10_relat_1(A_67, A_33) | ~v1_relat_1(k6_relat_1(A_33)) | ~v1_relat_1(A_67))), inference(superposition, [status(thm), theory('equality')], [c_22, c_246])).
% 8.58/2.95  tff(c_293, plain, (![A_74, A_75]: (k1_relat_1(k5_relat_1(A_74, k6_relat_1(A_75)))=k10_relat_1(A_74, A_75) | ~v1_relat_1(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_262])).
% 8.58/2.95  tff(c_315, plain, (![A_38, B_39]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_38, B_39)))=k10_relat_1(k6_relat_1(B_39), A_38) | ~v1_relat_1(k6_relat_1(B_39)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_293])).
% 8.58/2.95  tff(c_327, plain, (![B_39, A_38]: (k10_relat_1(k6_relat_1(B_39), A_38)=k3_xboole_0(A_38, B_39))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_315])).
% 8.58/2.95  tff(c_26, plain, (![A_34]: (k5_relat_1(A_34, k6_relat_1(k2_relat_1(A_34)))=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.58/2.95  tff(c_583, plain, (![B_92, C_93, A_94]: (k10_relat_1(k5_relat_1(B_92, C_93), A_94)=k10_relat_1(B_92, k10_relat_1(C_93, A_94)) | ~v1_relat_1(C_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.58/2.95  tff(c_617, plain, (![A_34, A_94]: (k10_relat_1(A_34, k10_relat_1(k6_relat_1(k2_relat_1(A_34)), A_94))=k10_relat_1(A_34, A_94) | ~v1_relat_1(k6_relat_1(k2_relat_1(A_34))) | ~v1_relat_1(A_34) | ~v1_relat_1(A_34))), inference(superposition, [status(thm), theory('equality')], [c_26, c_583])).
% 8.58/2.95  tff(c_625, plain, (![A_34, A_94]: (k10_relat_1(A_34, k3_xboole_0(A_94, k2_relat_1(A_34)))=k10_relat_1(A_34, A_94) | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_327, c_617])).
% 8.58/2.95  tff(c_79, plain, (![B_48, A_49]: (r1_tarski(k10_relat_1(B_48, A_49), k1_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.58/2.95  tff(c_82, plain, (![A_33, A_49]: (r1_tarski(k10_relat_1(k6_relat_1(A_33), A_49), A_33) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_79])).
% 8.58/2.95  tff(c_84, plain, (![A_33, A_49]: (r1_tarski(k10_relat_1(k6_relat_1(A_33), A_49), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_82])).
% 8.58/2.95  tff(c_253, plain, (![A_33, B_68]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_33), B_68)), A_33) | ~v1_relat_1(B_68) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_246, c_84])).
% 8.58/2.95  tff(c_269, plain, (![A_69, B_70]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_69), B_70)), A_69) | ~v1_relat_1(B_70))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_253])).
% 8.58/2.95  tff(c_272, plain, (![A_38, B_39]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_38, B_39))), B_39) | ~v1_relat_1(k6_relat_1(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_269])).
% 8.58/2.95  tff(c_281, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), B_39))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_272])).
% 8.58/2.95  tff(c_436, plain, (![B_85, A_86]: (k9_relat_1(B_85, k10_relat_1(B_85, A_86))=A_86 | ~r1_tarski(A_86, k2_relat_1(B_85)) | ~v1_funct_1(B_85) | ~v1_relat_1(B_85))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.58/2.95  tff(c_2864, plain, (![B_173, A_174]: (k9_relat_1(B_173, k10_relat_1(B_173, k3_xboole_0(A_174, k2_relat_1(B_173))))=k3_xboole_0(A_174, k2_relat_1(B_173)) | ~v1_funct_1(B_173) | ~v1_relat_1(B_173))), inference(resolution, [status(thm)], [c_281, c_436])).
% 8.58/2.95  tff(c_13588, plain, (![A_373, A_374]: (k9_relat_1(A_373, k10_relat_1(A_373, A_374))=k3_xboole_0(A_374, k2_relat_1(A_373)) | ~v1_funct_1(A_373) | ~v1_relat_1(A_373) | ~v1_relat_1(A_373))), inference(superposition, [status(thm), theory('equality')], [c_625, c_2864])).
% 8.58/2.95  tff(c_109, plain, (![A_54]: (k9_relat_1(A_54, k1_relat_1(A_54))=k2_relat_1(A_54) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.58/2.95  tff(c_36, plain, (k3_xboole_0('#skF_1', k9_relat_1('#skF_2', k1_relat_1('#skF_2')))!=k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.58/2.95  tff(c_115, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_109, c_36])).
% 8.58/2.95  tff(c_124, plain, (k9_relat_1('#skF_2', k10_relat_1('#skF_2', '#skF_1'))!=k3_xboole_0('#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_115])).
% 8.58/2.95  tff(c_13602, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13588, c_124])).
% 8.58/2.95  tff(c_13645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_13602])).
% 8.58/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.58/2.95  
% 8.58/2.95  Inference rules
% 8.58/2.95  ----------------------
% 8.58/2.95  #Ref     : 0
% 8.58/2.95  #Sup     : 3403
% 8.58/2.95  #Fact    : 0
% 8.58/2.95  #Define  : 0
% 8.58/2.95  #Split   : 0
% 8.58/2.95  #Chain   : 0
% 8.58/2.95  #Close   : 0
% 8.58/2.95  
% 8.58/2.95  Ordering : KBO
% 8.58/2.95  
% 8.58/2.95  Simplification rules
% 8.58/2.95  ----------------------
% 8.58/2.95  #Subsume      : 477
% 8.58/2.95  #Demod        : 4072
% 8.58/2.95  #Tautology    : 1170
% 8.58/2.95  #SimpNegUnit  : 0
% 8.58/2.95  #BackRed      : 2
% 8.58/2.95  
% 8.58/2.95  #Partial instantiations: 0
% 8.58/2.95  #Strategies tried      : 1
% 8.58/2.95  
% 8.58/2.95  Timing (in seconds)
% 8.58/2.95  ----------------------
% 8.58/2.95  Preprocessing        : 0.31
% 8.58/2.95  Parsing              : 0.17
% 8.58/2.95  CNF conversion       : 0.02
% 8.58/2.95  Main loop            : 1.86
% 8.58/2.95  Inferencing          : 0.53
% 8.58/2.95  Reduction            : 0.82
% 8.58/2.95  Demodulation         : 0.68
% 8.58/2.95  BG Simplification    : 0.07
% 8.58/2.95  Subsumption          : 0.36
% 8.58/2.95  Abstraction          : 0.11
% 8.58/2.95  MUC search           : 0.00
% 8.58/2.95  Cooper               : 0.00
% 8.58/2.95  Total                : 2.20
% 8.58/2.95  Index Insertion      : 0.00
% 8.58/2.95  Index Deletion       : 0.00
% 8.58/2.95  Index Matching       : 0.00
% 8.58/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------

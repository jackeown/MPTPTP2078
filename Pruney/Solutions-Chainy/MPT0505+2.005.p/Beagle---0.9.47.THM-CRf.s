%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:51 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   61 (  78 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 (  94 expanded)
%              Number of equality atoms :   33 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_97,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_97])).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    ! [A_18] : k1_relat_1(k6_relat_1(A_18)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_106,plain,(
    ! [A_37] :
      ( k7_relat_1(A_37,k1_relat_1(A_37)) = A_37
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_118,plain,(
    ! [A_18] :
      ( k7_relat_1(k6_relat_1(A_18),A_18) = k6_relat_1(A_18)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_106])).

tff(c_122,plain,(
    ! [A_18] : k7_relat_1(k6_relat_1(A_18),A_18) = k6_relat_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_175,plain,(
    ! [B_43,A_44] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_43,A_44)),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_181,plain,(
    ! [A_18] :
      ( r1_tarski(k1_relat_1(k6_relat_1(A_18)),A_18)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_175])).

tff(c_187,plain,(
    ! [A_18] : r1_tarski(A_18,A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_181])).

tff(c_235,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,C_50)
      | ~ r1_tarski(k2_xboole_0(A_49,B_51),C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_246,plain,(
    ! [A_49,B_51] : r1_tarski(A_49,k2_xboole_0(A_49,B_51)) ),
    inference(resolution,[status(thm)],[c_187,c_235])).

tff(c_288,plain,(
    ! [B_56,A_57] :
      ( k7_relat_1(B_56,A_57) = B_56
      | ~ r1_tarski(k1_relat_1(B_56),A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_303,plain,(
    ! [B_56,B_51] :
      ( k7_relat_1(B_56,k2_xboole_0(k1_relat_1(B_56),B_51)) = B_56
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_246,c_288])).

tff(c_605,plain,(
    ! [B_74,A_75] :
      ( k3_xboole_0(k1_relat_1(B_74),A_75) = k1_relat_1(k7_relat_1(B_74,A_75))
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_628,plain,(
    ! [A_18,A_75] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_18),A_75)) = k3_xboole_0(A_18,A_75)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_605])).

tff(c_633,plain,(
    ! [A_76,A_77] : k1_relat_1(k7_relat_1(k6_relat_1(A_76),A_77)) = k3_xboole_0(A_76,A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_628])).

tff(c_661,plain,(
    ! [A_76,B_51] :
      ( k3_xboole_0(A_76,k2_xboole_0(k1_relat_1(k6_relat_1(A_76)),B_51)) = k1_relat_1(k6_relat_1(A_76))
      | ~ v1_relat_1(k6_relat_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_633])).

tff(c_932,plain,(
    ! [A_92,B_93] : k3_xboole_0(A_92,k2_xboole_0(A_92,B_93)) = A_92 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_18,c_18,c_661])).

tff(c_982,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_932])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_137])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_158,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_10])).

tff(c_821,plain,(
    ! [C_87,A_88,B_89] :
      ( k7_relat_1(k7_relat_1(C_87,A_88),B_89) = k7_relat_1(C_87,k3_xboole_0(A_88,B_89))
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_844,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_30])).

tff(c_876,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_158,c_844])).

tff(c_994,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:26:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.76/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.45  
% 2.76/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.45  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.45  
% 2.87/1.45  %Foreground sorts:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Background operators:
% 2.87/1.45  
% 2.87/1.45  
% 2.87/1.45  %Foreground operators:
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.87/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.87/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.87/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.87/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.87/1.45  
% 2.87/1.46  tff(f_78, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.87/1.46  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.87/1.46  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.87/1.46  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.87/1.46  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.87/1.46  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.87/1.46  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.87/1.46  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.87/1.46  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.87/1.46  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.87/1.46  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.87/1.46  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.87/1.46  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.46  tff(c_97, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.46  tff(c_101, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_97])).
% 2.87/1.46  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.87/1.46  tff(c_18, plain, (![A_18]: (k1_relat_1(k6_relat_1(A_18))=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.87/1.46  tff(c_106, plain, (![A_37]: (k7_relat_1(A_37, k1_relat_1(A_37))=A_37 | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.87/1.46  tff(c_118, plain, (![A_18]: (k7_relat_1(k6_relat_1(A_18), A_18)=k6_relat_1(A_18) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_106])).
% 2.87/1.46  tff(c_122, plain, (![A_18]: (k7_relat_1(k6_relat_1(A_18), A_18)=k6_relat_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118])).
% 2.87/1.46  tff(c_175, plain, (![B_43, A_44]: (r1_tarski(k1_relat_1(k7_relat_1(B_43, A_44)), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.46  tff(c_181, plain, (![A_18]: (r1_tarski(k1_relat_1(k6_relat_1(A_18)), A_18) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_175])).
% 2.87/1.46  tff(c_187, plain, (![A_18]: (r1_tarski(A_18, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_181])).
% 2.87/1.46  tff(c_235, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, C_50) | ~r1_tarski(k2_xboole_0(A_49, B_51), C_50))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.46  tff(c_246, plain, (![A_49, B_51]: (r1_tarski(A_49, k2_xboole_0(A_49, B_51)))), inference(resolution, [status(thm)], [c_187, c_235])).
% 2.87/1.46  tff(c_288, plain, (![B_56, A_57]: (k7_relat_1(B_56, A_57)=B_56 | ~r1_tarski(k1_relat_1(B_56), A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.87/1.46  tff(c_303, plain, (![B_56, B_51]: (k7_relat_1(B_56, k2_xboole_0(k1_relat_1(B_56), B_51))=B_56 | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_246, c_288])).
% 2.87/1.46  tff(c_605, plain, (![B_74, A_75]: (k3_xboole_0(k1_relat_1(B_74), A_75)=k1_relat_1(k7_relat_1(B_74, A_75)) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.87/1.46  tff(c_628, plain, (![A_18, A_75]: (k1_relat_1(k7_relat_1(k6_relat_1(A_18), A_75))=k3_xboole_0(A_18, A_75) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_605])).
% 2.87/1.46  tff(c_633, plain, (![A_76, A_77]: (k1_relat_1(k7_relat_1(k6_relat_1(A_76), A_77))=k3_xboole_0(A_76, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_628])).
% 2.87/1.46  tff(c_661, plain, (![A_76, B_51]: (k3_xboole_0(A_76, k2_xboole_0(k1_relat_1(k6_relat_1(A_76)), B_51))=k1_relat_1(k6_relat_1(A_76)) | ~v1_relat_1(k6_relat_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_303, c_633])).
% 2.87/1.46  tff(c_932, plain, (![A_92, B_93]: (k3_xboole_0(A_92, k2_xboole_0(A_92, B_93))=A_92)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_18, c_18, c_661])).
% 2.87/1.46  tff(c_982, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_101, c_932])).
% 2.87/1.46  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.46  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.46  tff(c_137, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.46  tff(c_152, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_6, c_137])).
% 2.87/1.46  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.46  tff(c_158, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_152, c_10])).
% 2.87/1.46  tff(c_821, plain, (![C_87, A_88, B_89]: (k7_relat_1(k7_relat_1(C_87, A_88), B_89)=k7_relat_1(C_87, k3_xboole_0(A_88, B_89)) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.87/1.46  tff(c_30, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.46  tff(c_844, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_821, c_30])).
% 2.87/1.46  tff(c_876, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_158, c_844])).
% 2.87/1.46  tff(c_994, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_982, c_876])).
% 2.87/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.46  
% 2.87/1.46  Inference rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Ref     : 0
% 2.87/1.46  #Sup     : 224
% 2.87/1.46  #Fact    : 0
% 2.87/1.46  #Define  : 0
% 2.87/1.46  #Split   : 0
% 2.87/1.46  #Chain   : 0
% 2.87/1.46  #Close   : 0
% 2.87/1.46  
% 2.87/1.46  Ordering : KBO
% 2.87/1.46  
% 2.87/1.46  Simplification rules
% 2.87/1.46  ----------------------
% 2.87/1.46  #Subsume      : 12
% 2.87/1.46  #Demod        : 123
% 2.87/1.46  #Tautology    : 138
% 2.87/1.46  #SimpNegUnit  : 0
% 2.87/1.46  #BackRed      : 1
% 2.87/1.46  
% 2.87/1.46  #Partial instantiations: 0
% 2.87/1.46  #Strategies tried      : 1
% 2.87/1.46  
% 2.87/1.46  Timing (in seconds)
% 2.87/1.46  ----------------------
% 2.87/1.46  Preprocessing        : 0.31
% 2.87/1.46  Parsing              : 0.17
% 2.87/1.46  CNF conversion       : 0.02
% 2.87/1.46  Main loop            : 0.33
% 2.87/1.46  Inferencing          : 0.13
% 2.87/1.46  Reduction            : 0.11
% 2.87/1.46  Demodulation         : 0.09
% 2.87/1.46  BG Simplification    : 0.02
% 2.87/1.46  Subsumption          : 0.05
% 2.87/1.46  Abstraction          : 0.02
% 2.87/1.46  MUC search           : 0.00
% 2.87/1.47  Cooper               : 0.00
% 2.87/1.47  Total                : 0.67
% 2.87/1.47  Index Insertion      : 0.00
% 2.87/1.47  Index Deletion       : 0.00
% 2.87/1.47  Index Matching       : 0.00
% 2.87/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

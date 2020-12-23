%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:36 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  78 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_98,plain,(
    ! [A_35,B_36] :
      ( k5_relat_1(k6_relat_1(A_35),B_36) = k7_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_16] :
      ( k5_relat_1(A_16,k6_relat_1(k2_relat_1(A_16))) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112,plain,(
    ! [A_35] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_35))),A_35) = k6_relat_1(A_35)
      | ~ v1_relat_1(k6_relat_1(A_35))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_35)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_18])).

tff(c_129,plain,(
    ! [A_35] : k7_relat_1(k6_relat_1(A_35),A_35) = k6_relat_1(A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_14,c_112])).

tff(c_221,plain,(
    ! [C_44,A_45,B_46] :
      ( k7_relat_1(k7_relat_1(C_44,A_45),B_46) = k7_relat_1(C_44,k3_xboole_0(A_45,B_46))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_239,plain,(
    ! [A_35,B_46] :
      ( k7_relat_1(k6_relat_1(A_35),k3_xboole_0(A_35,B_46)) = k7_relat_1(k6_relat_1(A_35),B_46)
      | ~ v1_relat_1(k6_relat_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_221])).

tff(c_246,plain,(
    ! [A_47,B_48] : k7_relat_1(k6_relat_1(A_47),k3_xboole_0(A_47,B_48)) = k7_relat_1(k6_relat_1(A_47),B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_239])).

tff(c_146,plain,(
    ! [B_38,A_39] :
      ( k5_relat_1(B_38,k6_relat_1(A_39)) = B_38
      | ~ r1_tarski(k2_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [A_13,A_39] :
      ( k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_39)) = k6_relat_1(A_13)
      | ~ r1_tarski(A_13,A_39)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_146])).

tff(c_153,plain,(
    ! [A_40,A_41] :
      ( k5_relat_1(k6_relat_1(A_40),k6_relat_1(A_41)) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_159,plain,(
    ! [A_41,A_40] :
      ( k7_relat_1(k6_relat_1(A_41),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_41))
      | ~ r1_tarski(A_40,A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_20])).

tff(c_187,plain,(
    ! [A_41,A_40] :
      ( k7_relat_1(k6_relat_1(A_41),A_40) = k6_relat_1(A_40)
      | ~ r1_tarski(A_40,A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_159])).

tff(c_255,plain,(
    ! [A_47,B_48] :
      ( k7_relat_1(k6_relat_1(A_47),B_48) = k6_relat_1(k3_xboole_0(A_47,B_48))
      | ~ r1_tarski(k3_xboole_0(A_47,B_48),A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_187])).

tff(c_267,plain,(
    ! [A_47,B_48] : k7_relat_1(k6_relat_1(A_47),B_48) = k6_relat_1(k3_xboole_0(A_47,B_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_255])).

tff(c_26,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_26])).

tff(c_125,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_104])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:12:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.29  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.09/1.29  
% 2.09/1.29  %Foreground sorts:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Background operators:
% 2.09/1.29  
% 2.09/1.29  
% 2.09/1.29  %Foreground operators:
% 2.09/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.09/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.09/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.09/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.09/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.09/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.29  
% 2.09/1.30  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.09/1.30  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.09/1.30  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.09/1.30  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.09/1.30  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 2.09/1.30  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.09/1.30  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.09/1.30  tff(f_62, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.09/1.30  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.30  tff(c_22, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.30  tff(c_14, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.30  tff(c_98, plain, (![A_35, B_36]: (k5_relat_1(k6_relat_1(A_35), B_36)=k7_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.30  tff(c_18, plain, (![A_16]: (k5_relat_1(A_16, k6_relat_1(k2_relat_1(A_16)))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.30  tff(c_112, plain, (![A_35]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_35))), A_35)=k6_relat_1(A_35) | ~v1_relat_1(k6_relat_1(A_35)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_35)))))), inference(superposition, [status(thm), theory('equality')], [c_98, c_18])).
% 2.09/1.30  tff(c_129, plain, (![A_35]: (k7_relat_1(k6_relat_1(A_35), A_35)=k6_relat_1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_14, c_112])).
% 2.09/1.30  tff(c_221, plain, (![C_44, A_45, B_46]: (k7_relat_1(k7_relat_1(C_44, A_45), B_46)=k7_relat_1(C_44, k3_xboole_0(A_45, B_46)) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.30  tff(c_239, plain, (![A_35, B_46]: (k7_relat_1(k6_relat_1(A_35), k3_xboole_0(A_35, B_46))=k7_relat_1(k6_relat_1(A_35), B_46) | ~v1_relat_1(k6_relat_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_221])).
% 2.09/1.30  tff(c_246, plain, (![A_47, B_48]: (k7_relat_1(k6_relat_1(A_47), k3_xboole_0(A_47, B_48))=k7_relat_1(k6_relat_1(A_47), B_48))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_239])).
% 2.09/1.30  tff(c_146, plain, (![B_38, A_39]: (k5_relat_1(B_38, k6_relat_1(A_39))=B_38 | ~r1_tarski(k2_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.30  tff(c_149, plain, (![A_13, A_39]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_39))=k6_relat_1(A_13) | ~r1_tarski(A_13, A_39) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_146])).
% 2.09/1.30  tff(c_153, plain, (![A_40, A_41]: (k5_relat_1(k6_relat_1(A_40), k6_relat_1(A_41))=k6_relat_1(A_40) | ~r1_tarski(A_40, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_149])).
% 2.09/1.30  tff(c_20, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.30  tff(c_159, plain, (![A_41, A_40]: (k7_relat_1(k6_relat_1(A_41), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_41)) | ~r1_tarski(A_40, A_41))), inference(superposition, [status(thm), theory('equality')], [c_153, c_20])).
% 2.09/1.30  tff(c_187, plain, (![A_41, A_40]: (k7_relat_1(k6_relat_1(A_41), A_40)=k6_relat_1(A_40) | ~r1_tarski(A_40, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_159])).
% 2.09/1.30  tff(c_255, plain, (![A_47, B_48]: (k7_relat_1(k6_relat_1(A_47), B_48)=k6_relat_1(k3_xboole_0(A_47, B_48)) | ~r1_tarski(k3_xboole_0(A_47, B_48), A_47))), inference(superposition, [status(thm), theory('equality')], [c_246, c_187])).
% 2.09/1.30  tff(c_267, plain, (![A_47, B_48]: (k7_relat_1(k6_relat_1(A_47), B_48)=k6_relat_1(k3_xboole_0(A_47, B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_255])).
% 2.09/1.30  tff(c_26, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.30  tff(c_104, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_98, c_26])).
% 2.09/1.30  tff(c_125, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_104])).
% 2.09/1.30  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_125])).
% 2.09/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  Inference rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Ref     : 0
% 2.09/1.30  #Sup     : 61
% 2.09/1.30  #Fact    : 0
% 2.09/1.30  #Define  : 0
% 2.09/1.30  #Split   : 1
% 2.09/1.30  #Chain   : 0
% 2.09/1.30  #Close   : 0
% 2.09/1.30  
% 2.09/1.30  Ordering : KBO
% 2.09/1.30  
% 2.09/1.30  Simplification rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Subsume      : 2
% 2.09/1.30  #Demod        : 34
% 2.09/1.30  #Tautology    : 37
% 2.09/1.30  #SimpNegUnit  : 0
% 2.09/1.30  #BackRed      : 3
% 2.09/1.30  
% 2.09/1.30  #Partial instantiations: 0
% 2.09/1.30  #Strategies tried      : 1
% 2.09/1.30  
% 2.09/1.30  Timing (in seconds)
% 2.09/1.30  ----------------------
% 2.09/1.30  Preprocessing        : 0.30
% 2.09/1.30  Parsing              : 0.17
% 2.09/1.30  CNF conversion       : 0.02
% 2.09/1.30  Main loop            : 0.19
% 2.09/1.30  Inferencing          : 0.08
% 2.09/1.30  Reduction            : 0.06
% 2.09/1.30  Demodulation         : 0.05
% 2.09/1.30  BG Simplification    : 0.01
% 2.09/1.30  Subsumption          : 0.02
% 2.09/1.30  Abstraction          : 0.02
% 2.09/1.30  MUC search           : 0.00
% 2.09/1.30  Cooper               : 0.00
% 2.09/1.30  Total                : 0.52
% 2.09/1.30  Index Insertion      : 0.00
% 2.09/1.30  Index Deletion       : 0.00
% 2.09/1.30  Index Matching       : 0.00
% 2.09/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

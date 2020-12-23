%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:05 EST 2020

% Result     : Theorem 4.28s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :   45 (  67 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  73 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [B_28,A_29] : k1_setfam_1(k2_tarski(B_28,A_29)) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_78])).

tff(c_10,plain,(
    ! [A_9,B_10] : k1_setfam_1(k2_tarski(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_10])).

tff(c_215,plain,(
    ! [B_36,A_37] :
      ( k3_xboole_0(B_36,k2_zfmisc_1(A_37,k2_relat_1(B_36))) = k7_relat_1(B_36,A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_234,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(k7_relat_1(B_38,A_39),B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_237,plain,(
    ! [B_38,A_39] :
      ( k3_xboole_0(k7_relat_1(B_38,A_39),B_38) = k7_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(resolution,[status(thm)],[c_234,c_4])).

tff(c_242,plain,(
    ! [B_38,A_39] :
      ( k3_xboole_0(B_38,k7_relat_1(B_38,A_39)) = k7_relat_1(B_38,A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_237])).

tff(c_16,plain,(
    ! [A_16] :
      ( k7_relat_1(A_16,k1_relat_1(A_16)) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_279,plain,(
    ! [C_43,A_44,B_45] :
      ( k3_xboole_0(k7_relat_1(C_43,A_44),k7_relat_1(C_43,B_45)) = k7_relat_1(C_43,k3_xboole_0(A_44,B_45))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_318,plain,(
    ! [A_16,A_44] :
      ( k7_relat_1(A_16,k3_xboole_0(A_44,k1_relat_1(A_16))) = k3_xboole_0(k7_relat_1(A_16,A_44),A_16)
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_279])).

tff(c_2884,plain,(
    ! [A_100,A_101] :
      ( k7_relat_1(A_100,k3_xboole_0(A_101,k1_relat_1(A_100))) = k3_xboole_0(A_100,k7_relat_1(A_100,A_101))
      | ~ v1_relat_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_318])).

tff(c_18,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_18])).

tff(c_2927,plain,
    ( k3_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2884,c_155])).

tff(c_2965,plain,(
    k3_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_2927])).

tff(c_2970,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_2965])).

tff(c_2974,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2970])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:23:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.28/1.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.89  
% 4.28/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.90  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.28/1.90  
% 4.28/1.90  %Foreground sorts:
% 4.28/1.90  
% 4.28/1.90  
% 4.28/1.90  %Background operators:
% 4.28/1.90  
% 4.28/1.90  
% 4.28/1.90  %Foreground operators:
% 4.28/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.90  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.28/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.90  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.28/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.28/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.28/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.28/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.28/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.90  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.28/1.90  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.28/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.28/1.90  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.28/1.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.28/1.90  
% 4.28/1.91  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 4.28/1.91  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.28/1.91  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.28/1.91  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 4.28/1.91  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.28/1.91  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.28/1.91  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 4.28/1.91  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 4.28/1.91  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.28/1.91  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.28/1.91  tff(c_78, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.91  tff(c_93, plain, (![B_28, A_29]: (k1_setfam_1(k2_tarski(B_28, A_29))=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_6, c_78])).
% 4.28/1.91  tff(c_10, plain, (![A_9, B_10]: (k1_setfam_1(k2_tarski(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.28/1.91  tff(c_99, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_93, c_10])).
% 4.28/1.91  tff(c_215, plain, (![B_36, A_37]: (k3_xboole_0(B_36, k2_zfmisc_1(A_37, k2_relat_1(B_36)))=k7_relat_1(B_36, A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.28/1.91  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.28/1.91  tff(c_234, plain, (![B_38, A_39]: (r1_tarski(k7_relat_1(B_38, A_39), B_38) | ~v1_relat_1(B_38))), inference(superposition, [status(thm), theory('equality')], [c_215, c_2])).
% 4.28/1.91  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.91  tff(c_237, plain, (![B_38, A_39]: (k3_xboole_0(k7_relat_1(B_38, A_39), B_38)=k7_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(resolution, [status(thm)], [c_234, c_4])).
% 4.28/1.91  tff(c_242, plain, (![B_38, A_39]: (k3_xboole_0(B_38, k7_relat_1(B_38, A_39))=k7_relat_1(B_38, A_39) | ~v1_relat_1(B_38))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_237])).
% 4.28/1.91  tff(c_16, plain, (![A_16]: (k7_relat_1(A_16, k1_relat_1(A_16))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.28/1.91  tff(c_279, plain, (![C_43, A_44, B_45]: (k3_xboole_0(k7_relat_1(C_43, A_44), k7_relat_1(C_43, B_45))=k7_relat_1(C_43, k3_xboole_0(A_44, B_45)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.28/1.91  tff(c_318, plain, (![A_16, A_44]: (k7_relat_1(A_16, k3_xboole_0(A_44, k1_relat_1(A_16)))=k3_xboole_0(k7_relat_1(A_16, A_44), A_16) | ~v1_relat_1(A_16) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_16, c_279])).
% 4.28/1.91  tff(c_2884, plain, (![A_100, A_101]: (k7_relat_1(A_100, k3_xboole_0(A_101, k1_relat_1(A_100)))=k3_xboole_0(A_100, k7_relat_1(A_100, A_101)) | ~v1_relat_1(A_100) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_318])).
% 4.28/1.91  tff(c_18, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.28/1.91  tff(c_155, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_18])).
% 4.28/1.91  tff(c_2927, plain, (k3_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2884, c_155])).
% 4.28/1.91  tff(c_2965, plain, (k3_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_2927])).
% 4.28/1.91  tff(c_2970, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_242, c_2965])).
% 4.28/1.91  tff(c_2974, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_2970])).
% 4.28/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.28/1.91  
% 4.28/1.91  Inference rules
% 4.28/1.91  ----------------------
% 4.28/1.91  #Ref     : 0
% 4.28/1.91  #Sup     : 758
% 4.28/1.91  #Fact    : 0
% 4.28/1.91  #Define  : 0
% 4.28/1.91  #Split   : 0
% 4.28/1.91  #Chain   : 0
% 4.28/1.91  #Close   : 0
% 4.28/1.91  
% 4.28/1.91  Ordering : KBO
% 4.28/1.91  
% 4.28/1.91  Simplification rules
% 4.28/1.91  ----------------------
% 4.28/1.91  #Subsume      : 141
% 4.28/1.91  #Demod        : 903
% 4.28/1.91  #Tautology    : 421
% 4.28/1.91  #SimpNegUnit  : 0
% 4.28/1.91  #BackRed      : 0
% 4.28/1.91  
% 4.28/1.91  #Partial instantiations: 0
% 4.28/1.91  #Strategies tried      : 1
% 4.28/1.91  
% 4.28/1.91  Timing (in seconds)
% 4.28/1.91  ----------------------
% 4.28/1.91  Preprocessing        : 0.33
% 4.28/1.91  Parsing              : 0.17
% 4.28/1.91  CNF conversion       : 0.02
% 4.28/1.91  Main loop            : 0.78
% 4.28/1.91  Inferencing          : 0.24
% 4.28/1.91  Reduction            : 0.36
% 4.28/1.91  Demodulation         : 0.31
% 4.28/1.91  BG Simplification    : 0.03
% 4.28/1.91  Subsumption          : 0.12
% 4.28/1.91  Abstraction          : 0.05
% 4.28/1.91  MUC search           : 0.00
% 4.28/1.91  Cooper               : 0.00
% 4.28/1.91  Total                : 1.14
% 4.28/1.91  Index Insertion      : 0.00
% 4.28/1.91  Index Deletion       : 0.00
% 4.28/1.91  Index Matching       : 0.00
% 4.28/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------

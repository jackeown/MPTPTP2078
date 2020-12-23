%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:04 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :   50 (  79 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 120 expanded)
%              Number of equality atoms :   18 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_170,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(B_45,k2_zfmisc_1(A_46,k2_relat_1(B_45))) = k7_relat_1(B_45,A_46)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_179,plain,(
    ! [B_45,A_46] :
      ( r1_tarski(k7_relat_1(B_45,A_46),B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_212,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(k1_relat_1(A_56),k1_relat_1(B_57))
      | ~ r1_tarski(A_56,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_217,plain,(
    ! [A_58,B_59] :
      ( k7_relat_1(A_58,k1_relat_1(B_59)) = A_58
      | ~ r1_tarski(A_58,B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_212,c_22])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(k7_relat_1(C_16,A_14),B_15) = k7_relat_1(C_16,k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1259,plain,(
    ! [C_125,A_126,B_127] :
      ( k7_relat_1(C_125,k3_xboole_0(A_126,k1_relat_1(B_127))) = k7_relat_1(C_125,A_126)
      | ~ v1_relat_1(C_125)
      | ~ r1_tarski(k7_relat_1(C_125,A_126),B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(k7_relat_1(C_125,A_126)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_14])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_86,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(B_35,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_92,plain,(
    ! [B_35,A_34] : k3_xboole_0(B_35,A_34) = k3_xboole_0(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_10])).

tff(c_24,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_157,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_24])).

tff(c_1342,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1259,c_157])).

tff(c_1384,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1342])).

tff(c_1387,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1384])).

tff(c_1390,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1387])).

tff(c_1394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1390])).

tff(c_1395,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1384])).

tff(c_1399,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_179,c_1395])).

tff(c_1403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.76  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.77  
% 3.87/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.77  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.87/1.77  
% 3.87/1.77  %Foreground sorts:
% 3.87/1.77  
% 3.87/1.77  
% 3.87/1.77  %Background operators:
% 3.87/1.77  
% 3.87/1.77  
% 3.87/1.77  %Foreground operators:
% 3.87/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.77  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.87/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.87/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.87/1.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.87/1.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.87/1.77  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.77  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.87/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.87/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.87/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.87/1.77  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.87/1.77  
% 4.27/1.78  tff(f_69, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 4.27/1.78  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t96_relat_1)).
% 4.27/1.78  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.27/1.78  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.27/1.78  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 4.27/1.78  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.27/1.78  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 4.27/1.78  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.27/1.78  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.27/1.78  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.27/1.78  tff(c_170, plain, (![B_45, A_46]: (k3_xboole_0(B_45, k2_zfmisc_1(A_46, k2_relat_1(B_45)))=k7_relat_1(B_45, A_46) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.27/1.78  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.27/1.78  tff(c_179, plain, (![B_45, A_46]: (r1_tarski(k7_relat_1(B_45, A_46), B_45) | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_170, c_2])).
% 4.27/1.78  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.27/1.78  tff(c_212, plain, (![A_56, B_57]: (r1_tarski(k1_relat_1(A_56), k1_relat_1(B_57)) | ~r1_tarski(A_56, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.27/1.78  tff(c_22, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.27/1.78  tff(c_217, plain, (![A_58, B_59]: (k7_relat_1(A_58, k1_relat_1(B_59))=A_58 | ~r1_tarski(A_58, B_59) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_212, c_22])).
% 4.27/1.78  tff(c_14, plain, (![C_16, A_14, B_15]: (k7_relat_1(k7_relat_1(C_16, A_14), B_15)=k7_relat_1(C_16, k3_xboole_0(A_14, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.27/1.78  tff(c_1259, plain, (![C_125, A_126, B_127]: (k7_relat_1(C_125, k3_xboole_0(A_126, k1_relat_1(B_127)))=k7_relat_1(C_125, A_126) | ~v1_relat_1(C_125) | ~r1_tarski(k7_relat_1(C_125, A_126), B_127) | ~v1_relat_1(B_127) | ~v1_relat_1(k7_relat_1(C_125, A_126)))), inference(superposition, [status(thm), theory('equality')], [c_217, c_14])).
% 4.27/1.78  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.27/1.78  tff(c_62, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.78  tff(c_86, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(B_35, A_34))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 4.27/1.78  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.27/1.78  tff(c_92, plain, (![B_35, A_34]: (k3_xboole_0(B_35, A_34)=k3_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_86, c_10])).
% 4.27/1.78  tff(c_24, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.27/1.78  tff(c_157, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_24])).
% 4.27/1.78  tff(c_1342, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1259, c_157])).
% 4.27/1.78  tff(c_1384, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1342])).
% 4.27/1.78  tff(c_1387, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1384])).
% 4.27/1.78  tff(c_1390, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_1387])).
% 4.27/1.78  tff(c_1394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1390])).
% 4.27/1.78  tff(c_1395, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_1384])).
% 4.27/1.78  tff(c_1399, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_179, c_1395])).
% 4.27/1.78  tff(c_1403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1399])).
% 4.27/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.78  
% 4.27/1.78  Inference rules
% 4.27/1.78  ----------------------
% 4.27/1.78  #Ref     : 0
% 4.27/1.78  #Sup     : 388
% 4.27/1.78  #Fact    : 0
% 4.27/1.78  #Define  : 0
% 4.27/1.78  #Split   : 1
% 4.27/1.78  #Chain   : 0
% 4.27/1.78  #Close   : 0
% 4.27/1.78  
% 4.27/1.78  Ordering : KBO
% 4.27/1.78  
% 4.27/1.78  Simplification rules
% 4.27/1.78  ----------------------
% 4.27/1.78  #Subsume      : 90
% 4.27/1.78  #Demod        : 27
% 4.27/1.78  #Tautology    : 54
% 4.27/1.78  #SimpNegUnit  : 0
% 4.27/1.78  #BackRed      : 0
% 4.27/1.78  
% 4.27/1.78  #Partial instantiations: 0
% 4.27/1.78  #Strategies tried      : 1
% 4.27/1.78  
% 4.27/1.78  Timing (in seconds)
% 4.27/1.78  ----------------------
% 4.27/1.78  Preprocessing        : 0.29
% 4.27/1.78  Parsing              : 0.15
% 4.27/1.78  CNF conversion       : 0.02
% 4.27/1.78  Main loop            : 0.70
% 4.27/1.78  Inferencing          : 0.26
% 4.27/1.79  Reduction            : 0.22
% 4.27/1.79  Demodulation         : 0.17
% 4.27/1.79  BG Simplification    : 0.04
% 4.27/1.79  Subsumption          : 0.15
% 4.27/1.79  Abstraction          : 0.04
% 4.27/1.79  MUC search           : 0.00
% 4.27/1.79  Cooper               : 0.00
% 4.27/1.79  Total                : 1.02
% 4.27/1.79  Index Insertion      : 0.00
% 4.27/1.79  Index Deletion       : 0.00
% 4.27/1.79  Index Matching       : 0.00
% 4.27/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------

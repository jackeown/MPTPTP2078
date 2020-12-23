%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:44 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   44 (  54 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  73 expanded)
%              Number of equality atoms :   17 (  27 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [A_4] : r1_tarski(A_4,k1_zfmisc_1(k3_tarski(A_4))) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_5,B_6] : k6_subset_1(A_5,B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(C_14,k6_subset_1(A_12,B_13)) = k6_subset_1(C_14,k7_relat_1(C_14,B_13))
      | ~ r1_tarski(k1_relat_1(C_14),A_12)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_49,plain,(
    ! [C_29,A_30,B_31] :
      ( k7_relat_1(C_29,k4_xboole_0(A_30,B_31)) = k4_xboole_0(C_29,k7_relat_1(C_29,B_31))
      | ~ r1_tarski(k1_relat_1(C_29),A_30)
      | ~ v1_relat_1(C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_12])).

tff(c_56,plain,(
    ! [C_32,B_33] :
      ( k7_relat_1(C_32,k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_32))),B_33)) = k4_xboole_0(C_32,k7_relat_1(C_32,B_33))
      | ~ v1_relat_1(C_32) ) ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_65,plain,(
    ! [C_32,B_33] :
      ( v1_relat_1(k4_xboole_0(C_32,k7_relat_1(C_32,B_33)))
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_8])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,k4_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k6_subset_1(B_16,k7_relat_1(B_16,A_15))) = k6_subset_1(k1_relat_1(B_16),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_37,plain,(
    ! [B_27,A_28] :
      ( k1_relat_1(k4_xboole_0(B_27,k7_relat_1(B_27,A_28))) = k4_xboole_0(k1_relat_1(B_27),A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_14])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( k7_relat_1(A_9,B_11) = k1_xboole_0
      | ~ r1_xboole_0(B_11,k1_relat_1(A_9))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_123,plain,(
    ! [B_42,A_43,B_44] :
      ( k7_relat_1(k4_xboole_0(B_42,k7_relat_1(B_42,A_43)),B_44) = k1_xboole_0
      | ~ r1_xboole_0(B_44,k4_xboole_0(k1_relat_1(B_42),A_43))
      | ~ v1_relat_1(k4_xboole_0(B_42,k7_relat_1(B_42,A_43)))
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_10])).

tff(c_134,plain,(
    ! [B_45,B_46,A_47] :
      ( k7_relat_1(k4_xboole_0(B_45,k7_relat_1(B_45,B_46)),A_47) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_45,k7_relat_1(B_45,B_46)))
      | ~ v1_relat_1(B_45)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_123])).

tff(c_140,plain,(
    ! [C_48,B_49,A_50] :
      ( k7_relat_1(k4_xboole_0(C_48,k7_relat_1(C_48,B_49)),A_50) = k1_xboole_0
      | ~ r1_tarski(A_50,B_49)
      | ~ v1_relat_1(C_48) ) ),
    inference(resolution,[status(thm)],[c_65,c_134])).

tff(c_16,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_23,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_16])).

tff(c_168,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_23])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:42:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.22  
% 1.96/1.22  %Foreground sorts:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Background operators:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Foreground operators:
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.22  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.96/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.22  
% 2.10/1.23  tff(f_61, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 2.10/1.23  tff(f_31, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.10/1.23  tff(f_33, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.10/1.23  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t211_relat_1)).
% 2.10/1.23  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.10/1.23  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.10/1.23  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 2.10/1.23  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 2.10/1.23  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.23  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.23  tff(c_4, plain, (![A_4]: (r1_tarski(A_4, k1_zfmisc_1(k3_tarski(A_4))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.23  tff(c_6, plain, (![A_5, B_6]: (k6_subset_1(A_5, B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.23  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(C_14, k6_subset_1(A_12, B_13))=k6_subset_1(C_14, k7_relat_1(C_14, B_13)) | ~r1_tarski(k1_relat_1(C_14), A_12) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.23  tff(c_49, plain, (![C_29, A_30, B_31]: (k7_relat_1(C_29, k4_xboole_0(A_30, B_31))=k4_xboole_0(C_29, k7_relat_1(C_29, B_31)) | ~r1_tarski(k1_relat_1(C_29), A_30) | ~v1_relat_1(C_29))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_12])).
% 2.10/1.23  tff(c_56, plain, (![C_32, B_33]: (k7_relat_1(C_32, k4_xboole_0(k1_zfmisc_1(k3_tarski(k1_relat_1(C_32))), B_33))=k4_xboole_0(C_32, k7_relat_1(C_32, B_33)) | ~v1_relat_1(C_32))), inference(resolution, [status(thm)], [c_4, c_49])).
% 2.10/1.23  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.23  tff(c_65, plain, (![C_32, B_33]: (v1_relat_1(k4_xboole_0(C_32, k7_relat_1(C_32, B_33))) | ~v1_relat_1(C_32) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_56, c_8])).
% 2.10/1.23  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, k4_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.10/1.23  tff(c_14, plain, (![B_16, A_15]: (k1_relat_1(k6_subset_1(B_16, k7_relat_1(B_16, A_15)))=k6_subset_1(k1_relat_1(B_16), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.23  tff(c_37, plain, (![B_27, A_28]: (k1_relat_1(k4_xboole_0(B_27, k7_relat_1(B_27, A_28)))=k4_xboole_0(k1_relat_1(B_27), A_28) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_14])).
% 2.10/1.23  tff(c_10, plain, (![A_9, B_11]: (k7_relat_1(A_9, B_11)=k1_xboole_0 | ~r1_xboole_0(B_11, k1_relat_1(A_9)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.23  tff(c_123, plain, (![B_42, A_43, B_44]: (k7_relat_1(k4_xboole_0(B_42, k7_relat_1(B_42, A_43)), B_44)=k1_xboole_0 | ~r1_xboole_0(B_44, k4_xboole_0(k1_relat_1(B_42), A_43)) | ~v1_relat_1(k4_xboole_0(B_42, k7_relat_1(B_42, A_43))) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_37, c_10])).
% 2.10/1.23  tff(c_134, plain, (![B_45, B_46, A_47]: (k7_relat_1(k4_xboole_0(B_45, k7_relat_1(B_45, B_46)), A_47)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_45, k7_relat_1(B_45, B_46))) | ~v1_relat_1(B_45) | ~r1_tarski(A_47, B_46))), inference(resolution, [status(thm)], [c_2, c_123])).
% 2.10/1.23  tff(c_140, plain, (![C_48, B_49, A_50]: (k7_relat_1(k4_xboole_0(C_48, k7_relat_1(C_48, B_49)), A_50)=k1_xboole_0 | ~r1_tarski(A_50, B_49) | ~v1_relat_1(C_48))), inference(resolution, [status(thm)], [c_65, c_134])).
% 2.10/1.23  tff(c_16, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.10/1.23  tff(c_23, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_16])).
% 2.10/1.23  tff(c_168, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_140, c_23])).
% 2.10/1.23  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_168])).
% 2.10/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  Inference rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Ref     : 0
% 2.10/1.23  #Sup     : 46
% 2.10/1.23  #Fact    : 0
% 2.10/1.23  #Define  : 0
% 2.10/1.23  #Split   : 0
% 2.10/1.23  #Chain   : 0
% 2.10/1.23  #Close   : 0
% 2.10/1.23  
% 2.10/1.23  Ordering : KBO
% 2.10/1.23  
% 2.10/1.23  Simplification rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Subsume      : 1
% 2.10/1.23  #Demod        : 7
% 2.10/1.23  #Tautology    : 11
% 2.10/1.23  #SimpNegUnit  : 0
% 2.10/1.23  #BackRed      : 0
% 2.10/1.23  
% 2.10/1.23  #Partial instantiations: 0
% 2.10/1.23  #Strategies tried      : 1
% 2.10/1.23  
% 2.10/1.23  Timing (in seconds)
% 2.10/1.23  ----------------------
% 2.10/1.24  Preprocessing        : 0.29
% 2.10/1.24  Parsing              : 0.15
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.19
% 2.10/1.24  Inferencing          : 0.08
% 2.10/1.24  Reduction            : 0.05
% 2.10/1.24  Demodulation         : 0.04
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.03
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.51
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

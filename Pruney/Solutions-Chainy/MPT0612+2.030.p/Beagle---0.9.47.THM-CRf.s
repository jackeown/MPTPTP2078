%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:45 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   49 (  57 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   66 (  80 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(c_24,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [B_7,A_6] : r1_xboole_0(B_7,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_8,c_40])).

tff(c_49,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = A_29
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    ! [B_7,A_6] : k4_xboole_0(B_7,k4_xboole_0(A_6,B_7)) = B_7 ),
    inference(resolution,[status(thm)],[c_43,c_49])).

tff(c_100,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_xboole_0(A_37,C_38)
      | ~ r1_tarski(A_37,k4_xboole_0(B_39,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_49,A_50,B_51] :
      ( r1_xboole_0(A_49,k4_xboole_0(A_50,B_51))
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_100])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_189,plain,(
    ! [A_49,A_50,B_51] :
      ( k4_xboole_0(A_49,k4_xboole_0(A_50,B_51)) = A_49
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(resolution,[status(thm)],[c_177,c_10])).

tff(c_26,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k4_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k6_subset_1(B_18,k7_relat_1(B_18,A_17))) = k6_subset_1(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_314,plain,(
    ! [B_66,A_67] :
      ( k1_relat_1(k4_xboole_0(B_66,k7_relat_1(B_66,A_67))) = k4_xboole_0(k1_relat_1(B_66),A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_20])).

tff(c_18,plain,(
    ! [A_14,B_16] :
      ( k7_relat_1(A_14,B_16) = k1_xboole_0
      | ~ r1_xboole_0(B_16,k1_relat_1(A_14))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_561,plain,(
    ! [B_89,A_90,B_91] :
      ( k7_relat_1(k4_xboole_0(B_89,k7_relat_1(B_89,A_90)),B_91) = k1_xboole_0
      | ~ r1_xboole_0(B_91,k4_xboole_0(k1_relat_1(B_89),A_90))
      | ~ v1_relat_1(k4_xboole_0(B_89,k7_relat_1(B_89,A_90)))
      | ~ v1_relat_1(B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_18])).

tff(c_1213,plain,(
    ! [B_158,A_159,A_160] :
      ( k7_relat_1(k4_xboole_0(B_158,k7_relat_1(B_158,A_159)),A_160) = k1_xboole_0
      | ~ v1_relat_1(k4_xboole_0(B_158,k7_relat_1(B_158,A_159)))
      | ~ v1_relat_1(B_158)
      | k4_xboole_0(A_160,k4_xboole_0(k1_relat_1(B_158),A_159)) != A_160 ) ),
    inference(resolution,[status(thm)],[c_12,c_561])).

tff(c_1671,plain,(
    ! [A_212,A_213,A_214] :
      ( k7_relat_1(k4_xboole_0(A_212,k7_relat_1(A_212,A_213)),A_214) = k1_xboole_0
      | k4_xboole_0(A_214,k4_xboole_0(k1_relat_1(A_212),A_213)) != A_214
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_16,c_1213])).

tff(c_22,plain,(
    k7_relat_1(k6_subset_1('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    k7_relat_1(k4_xboole_0('#skF_3',k7_relat_1('#skF_3','#skF_2')),'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_1716,plain,
    ( k4_xboole_0('#skF_1',k4_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1671,c_28])).

tff(c_1763,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0(k1_relat_1('#skF_3'),'#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1716])).

tff(c_1782,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_1763])).

tff(c_1788,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:51:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.66  
% 3.81/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.66  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.81/1.66  
% 3.81/1.66  %Foreground sorts:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Background operators:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Foreground operators:
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.81/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.81/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.81/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.81/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.81/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.81/1.66  
% 3.81/1.68  tff(f_65, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t216_relat_1)).
% 3.81/1.68  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.81/1.68  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.81/1.68  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.81/1.68  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.81/1.68  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_relat_1)).
% 3.81/1.68  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.81/1.68  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t212_relat_1)).
% 3.81/1.68  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 3.81/1.68  tff(c_24, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.68  tff(c_8, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.81/1.68  tff(c_40, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.81/1.68  tff(c_43, plain, (![B_7, A_6]: (r1_xboole_0(B_7, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_8, c_40])).
% 3.81/1.68  tff(c_49, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=A_29 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.81/1.68  tff(c_56, plain, (![B_7, A_6]: (k4_xboole_0(B_7, k4_xboole_0(A_6, B_7))=B_7)), inference(resolution, [status(thm)], [c_43, c_49])).
% 3.81/1.68  tff(c_100, plain, (![A_37, C_38, B_39]: (r1_xboole_0(A_37, C_38) | ~r1_tarski(A_37, k4_xboole_0(B_39, C_38)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.81/1.68  tff(c_177, plain, (![A_49, A_50, B_51]: (r1_xboole_0(A_49, k4_xboole_0(A_50, B_51)) | ~r1_tarski(A_49, B_51))), inference(superposition, [status(thm), theory('equality')], [c_56, c_100])).
% 3.81/1.68  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.81/1.68  tff(c_189, plain, (![A_49, A_50, B_51]: (k4_xboole_0(A_49, k4_xboole_0(A_50, B_51))=A_49 | ~r1_tarski(A_49, B_51))), inference(resolution, [status(thm)], [c_177, c_10])).
% 3.81/1.68  tff(c_26, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.68  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k4_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.81/1.68  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.81/1.68  tff(c_14, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.81/1.68  tff(c_20, plain, (![B_18, A_17]: (k1_relat_1(k6_subset_1(B_18, k7_relat_1(B_18, A_17)))=k6_subset_1(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.81/1.68  tff(c_314, plain, (![B_66, A_67]: (k1_relat_1(k4_xboole_0(B_66, k7_relat_1(B_66, A_67)))=k4_xboole_0(k1_relat_1(B_66), A_67) | ~v1_relat_1(B_66))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_20])).
% 3.81/1.68  tff(c_18, plain, (![A_14, B_16]: (k7_relat_1(A_14, B_16)=k1_xboole_0 | ~r1_xboole_0(B_16, k1_relat_1(A_14)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.81/1.68  tff(c_561, plain, (![B_89, A_90, B_91]: (k7_relat_1(k4_xboole_0(B_89, k7_relat_1(B_89, A_90)), B_91)=k1_xboole_0 | ~r1_xboole_0(B_91, k4_xboole_0(k1_relat_1(B_89), A_90)) | ~v1_relat_1(k4_xboole_0(B_89, k7_relat_1(B_89, A_90))) | ~v1_relat_1(B_89))), inference(superposition, [status(thm), theory('equality')], [c_314, c_18])).
% 3.81/1.68  tff(c_1213, plain, (![B_158, A_159, A_160]: (k7_relat_1(k4_xboole_0(B_158, k7_relat_1(B_158, A_159)), A_160)=k1_xboole_0 | ~v1_relat_1(k4_xboole_0(B_158, k7_relat_1(B_158, A_159))) | ~v1_relat_1(B_158) | k4_xboole_0(A_160, k4_xboole_0(k1_relat_1(B_158), A_159))!=A_160)), inference(resolution, [status(thm)], [c_12, c_561])).
% 3.81/1.68  tff(c_1671, plain, (![A_212, A_213, A_214]: (k7_relat_1(k4_xboole_0(A_212, k7_relat_1(A_212, A_213)), A_214)=k1_xboole_0 | k4_xboole_0(A_214, k4_xboole_0(k1_relat_1(A_212), A_213))!=A_214 | ~v1_relat_1(A_212))), inference(resolution, [status(thm)], [c_16, c_1213])).
% 3.81/1.68  tff(c_22, plain, (k7_relat_1(k6_subset_1('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.68  tff(c_28, plain, (k7_relat_1(k4_xboole_0('#skF_3', k7_relat_1('#skF_3', '#skF_2')), '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 3.81/1.68  tff(c_1716, plain, (k4_xboole_0('#skF_1', k4_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1671, c_28])).
% 3.81/1.68  tff(c_1763, plain, (k4_xboole_0('#skF_1', k4_xboole_0(k1_relat_1('#skF_3'), '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1716])).
% 3.81/1.68  tff(c_1782, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_189, c_1763])).
% 3.81/1.68  tff(c_1788, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1782])).
% 3.81/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.68  
% 3.81/1.68  Inference rules
% 3.81/1.68  ----------------------
% 3.81/1.68  #Ref     : 0
% 3.81/1.68  #Sup     : 519
% 3.81/1.68  #Fact    : 0
% 3.81/1.68  #Define  : 0
% 3.81/1.68  #Split   : 2
% 3.81/1.68  #Chain   : 0
% 3.81/1.68  #Close   : 0
% 3.81/1.68  
% 3.81/1.68  Ordering : KBO
% 3.81/1.68  
% 3.81/1.68  Simplification rules
% 3.81/1.68  ----------------------
% 3.81/1.68  #Subsume      : 182
% 3.81/1.68  #Demod        : 40
% 3.81/1.68  #Tautology    : 105
% 3.81/1.68  #SimpNegUnit  : 0
% 3.81/1.68  #BackRed      : 0
% 3.81/1.68  
% 3.81/1.68  #Partial instantiations: 0
% 3.81/1.68  #Strategies tried      : 1
% 3.81/1.68  
% 3.81/1.68  Timing (in seconds)
% 3.81/1.68  ----------------------
% 3.81/1.68  Preprocessing        : 0.29
% 3.81/1.68  Parsing              : 0.15
% 3.81/1.68  CNF conversion       : 0.02
% 3.81/1.68  Main loop            : 0.62
% 3.81/1.68  Inferencing          : 0.21
% 3.81/1.68  Reduction            : 0.16
% 3.81/1.68  Demodulation         : 0.11
% 3.81/1.68  BG Simplification    : 0.03
% 3.81/1.68  Subsumption          : 0.18
% 3.81/1.68  Abstraction          : 0.03
% 3.81/1.68  MUC search           : 0.00
% 3.81/1.68  Cooper               : 0.00
% 3.81/1.68  Total                : 0.94
% 3.81/1.68  Index Insertion      : 0.00
% 3.81/1.68  Index Deletion       : 0.00
% 3.81/1.68  Index Matching       : 0.00
% 3.81/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

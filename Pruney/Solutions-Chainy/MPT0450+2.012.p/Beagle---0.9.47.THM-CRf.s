%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:38 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 2.92s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 125 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   91 ( 232 expanded)
%              Number of equality atoms :    7 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_17,C_19,B_18] :
      ( r1_tarski(k2_xboole_0(A_17,C_19),B_18)
      | ~ r1_tarski(C_19,B_18)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_46,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_585,plain,(
    ! [A_107,B_108] :
      ( k2_xboole_0(A_107,B_108) = A_107
      | ~ r1_tarski(k2_xboole_0(A_107,B_108),A_107) ) ),
    inference(resolution,[status(thm)],[c_18,c_46])).

tff(c_589,plain,(
    ! [B_18,C_19] :
      ( k2_xboole_0(B_18,C_19) = B_18
      | ~ r1_tarski(C_19,B_18)
      | ~ r1_tarski(B_18,B_18) ) ),
    inference(resolution,[status(thm)],[c_20,c_585])).

tff(c_598,plain,(
    ! [B_109,C_110] :
      ( k2_xboole_0(B_109,C_110) = B_109
      | ~ r1_tarski(C_110,B_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_589])).

tff(c_629,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_598])).

tff(c_689,plain,(
    ! [B_114] : k2_xboole_0(B_114,B_114) = B_114 ),
    inference(resolution,[status(thm)],[c_6,c_598])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] : r1_tarski(k2_xboole_0(k3_xboole_0(A_12,B_13),k3_xboole_0(A_12,C_14)),k2_xboole_0(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_696,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),k2_xboole_0(B_13,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_16])).

tff(c_825,plain,(
    ! [A_116,B_117] : r1_tarski(k3_xboole_0(A_116,B_117),B_117) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_696])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_112,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_116,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(A_20)
      | ~ v1_relat_1(B_21)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_861,plain,(
    ! [A_116,B_117] :
      ( v1_relat_1(k3_xboole_0(A_116,B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_825,c_116])).

tff(c_743,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_696])).

tff(c_1105,plain,(
    ! [A_124,B_125] :
      ( r1_tarski(k3_relat_1(A_124),k3_relat_1(B_125))
      | ~ r1_tarski(A_124,B_125)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [A_54,B_55] :
      ( v1_relat_1(A_54)
      | ~ v1_relat_1(B_55)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_24,c_112])).

tff(c_154,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k3_xboole_0(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_133])).

tff(c_294,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k3_relat_1(A_83),k3_relat_1(B_84))
      | ~ r1_tarski(A_83,B_84)
      | ~ v1_relat_1(B_84)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_117,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,k3_xboole_0(B_52,C_53))
      | ~ r1_tarski(A_51,C_53)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_131,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_117,c_30])).

tff(c_165,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_300,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_294,c_165])).

tff(c_309,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10,c_300])).

tff(c_314,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_154,c_309])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_314])).

tff(c_319,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_1114,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1105,c_319])).

tff(c_1124,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_743,c_1114])).

tff(c_1129,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_861,c_1124])).

tff(c_1136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.41  
% 2.92/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.41  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k3_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.92/1.41  
% 2.92/1.41  %Foreground sorts:
% 2.92/1.41  
% 2.92/1.41  
% 2.92/1.41  %Background operators:
% 2.92/1.41  
% 2.92/1.41  
% 2.92/1.41  %Foreground operators:
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.41  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.92/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.41  
% 2.92/1.43  tff(f_83, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.92/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.92/1.43  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.92/1.43  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.92/1.43  tff(f_47, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.92/1.43  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.92/1.43  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.92/1.43  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.92/1.43  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.92/1.43  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.92/1.43  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.92/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.43  tff(c_20, plain, (![A_17, C_19, B_18]: (r1_tarski(k2_xboole_0(A_17, C_19), B_18) | ~r1_tarski(C_19, B_18) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.92/1.43  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.92/1.43  tff(c_46, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.92/1.43  tff(c_585, plain, (![A_107, B_108]: (k2_xboole_0(A_107, B_108)=A_107 | ~r1_tarski(k2_xboole_0(A_107, B_108), A_107))), inference(resolution, [status(thm)], [c_18, c_46])).
% 2.92/1.43  tff(c_589, plain, (![B_18, C_19]: (k2_xboole_0(B_18, C_19)=B_18 | ~r1_tarski(C_19, B_18) | ~r1_tarski(B_18, B_18))), inference(resolution, [status(thm)], [c_20, c_585])).
% 2.92/1.43  tff(c_598, plain, (![B_109, C_110]: (k2_xboole_0(B_109, C_110)=B_109 | ~r1_tarski(C_110, B_109))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_589])).
% 2.92/1.43  tff(c_629, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_598])).
% 2.92/1.43  tff(c_689, plain, (![B_114]: (k2_xboole_0(B_114, B_114)=B_114)), inference(resolution, [status(thm)], [c_6, c_598])).
% 2.92/1.43  tff(c_16, plain, (![A_12, B_13, C_14]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_12, B_13), k3_xboole_0(A_12, C_14)), k2_xboole_0(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.92/1.43  tff(c_696, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), k2_xboole_0(B_13, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_689, c_16])).
% 2.92/1.43  tff(c_825, plain, (![A_116, B_117]: (r1_tarski(k3_xboole_0(A_116, B_117), B_117))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_696])).
% 2.92/1.43  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.92/1.43  tff(c_112, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.92/1.43  tff(c_116, plain, (![A_20, B_21]: (v1_relat_1(A_20) | ~v1_relat_1(B_21) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_24, c_112])).
% 2.92/1.43  tff(c_861, plain, (![A_116, B_117]: (v1_relat_1(k3_xboole_0(A_116, B_117)) | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_825, c_116])).
% 2.92/1.43  tff(c_743, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), B_13))), inference(demodulation, [status(thm), theory('equality')], [c_629, c_696])).
% 2.92/1.43  tff(c_1105, plain, (![A_124, B_125]: (r1_tarski(k3_relat_1(A_124), k3_relat_1(B_125)) | ~r1_tarski(A_124, B_125) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.92/1.43  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.92/1.43  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.92/1.43  tff(c_133, plain, (![A_54, B_55]: (v1_relat_1(A_54) | ~v1_relat_1(B_55) | ~r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_24, c_112])).
% 2.92/1.43  tff(c_154, plain, (![A_6, B_7]: (v1_relat_1(k3_xboole_0(A_6, B_7)) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_10, c_133])).
% 2.92/1.43  tff(c_294, plain, (![A_83, B_84]: (r1_tarski(k3_relat_1(A_83), k3_relat_1(B_84)) | ~r1_tarski(A_83, B_84) | ~v1_relat_1(B_84) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.92/1.43  tff(c_117, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, k3_xboole_0(B_52, C_53)) | ~r1_tarski(A_51, C_53) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.92/1.43  tff(c_30, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.92/1.43  tff(c_131, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_117, c_30])).
% 2.92/1.43  tff(c_165, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_131])).
% 2.92/1.43  tff(c_300, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_294, c_165])).
% 2.92/1.43  tff(c_309, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10, c_300])).
% 2.92/1.43  tff(c_314, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_154, c_309])).
% 2.92/1.43  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_314])).
% 2.92/1.43  tff(c_319, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_131])).
% 2.92/1.43  tff(c_1114, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1105, c_319])).
% 2.92/1.43  tff(c_1124, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_743, c_1114])).
% 2.92/1.43  tff(c_1129, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_861, c_1124])).
% 2.92/1.43  tff(c_1136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1129])).
% 2.92/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.92/1.43  
% 2.92/1.43  Inference rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Ref     : 0
% 2.92/1.43  #Sup     : 260
% 2.92/1.43  #Fact    : 0
% 2.92/1.43  #Define  : 0
% 2.92/1.43  #Split   : 4
% 2.92/1.43  #Chain   : 0
% 2.92/1.43  #Close   : 0
% 2.92/1.43  
% 2.92/1.43  Ordering : KBO
% 2.92/1.43  
% 2.92/1.43  Simplification rules
% 2.92/1.43  ----------------------
% 2.92/1.43  #Subsume      : 21
% 2.92/1.43  #Demod        : 118
% 2.92/1.43  #Tautology    : 142
% 2.92/1.43  #SimpNegUnit  : 6
% 2.92/1.43  #BackRed      : 2
% 2.92/1.43  
% 2.92/1.43  #Partial instantiations: 0
% 2.92/1.43  #Strategies tried      : 1
% 2.92/1.43  
% 2.92/1.43  Timing (in seconds)
% 2.92/1.43  ----------------------
% 2.92/1.43  Preprocessing        : 0.28
% 2.92/1.43  Parsing              : 0.16
% 2.92/1.43  CNF conversion       : 0.02
% 2.92/1.43  Main loop            : 0.37
% 2.92/1.43  Inferencing          : 0.14
% 2.92/1.43  Reduction            : 0.11
% 2.92/1.43  Demodulation         : 0.08
% 2.92/1.43  BG Simplification    : 0.02
% 2.92/1.43  Subsumption          : 0.07
% 2.92/1.43  Abstraction          : 0.02
% 2.92/1.43  MUC search           : 0.00
% 2.92/1.43  Cooper               : 0.00
% 2.92/1.43  Total                : 0.68
% 2.92/1.43  Index Insertion      : 0.00
% 2.92/1.43  Index Deletion       : 0.00
% 2.92/1.43  Index Matching       : 0.00
% 2.92/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

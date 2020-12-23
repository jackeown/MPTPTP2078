%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:23 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   57 (  99 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 137 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k3_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k2_xboole_0(k3_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)),k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_101,plain,(
    ! [A_56,B_57,C_58] : r1_tarski(k3_xboole_0(A_56,k2_xboole_0(B_57,C_58)),k2_xboole_0(B_57,C_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_107,plain,(
    ! [A_56,A_14,B_15] : r1_tarski(k3_xboole_0(A_56,A_14),k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_101])).

tff(c_124,plain,(
    ! [A_62,A_63] : r1_tarski(k3_xboole_0(A_62,A_63),A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_107])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_81,plain,(
    ! [B_48,A_49] :
      ( v1_relat_1(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    ! [A_25,B_26] :
      ( v1_relat_1(A_25)
      | ~ v1_relat_1(B_26)
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_128,plain,(
    ! [A_62,A_63] :
      ( v1_relat_1(k3_xboole_0(A_62,A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(resolution,[status(thm)],[c_124,c_85])).

tff(c_112,plain,(
    ! [A_56,A_14] : r1_tarski(k3_xboole_0(A_56,A_14),A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_107])).

tff(c_28,plain,(
    ! [A_30,B_32] :
      ( r1_tarski(k2_relat_1(A_30),k2_relat_1(B_32))
      | ~ r1_tarski(A_30,B_32)
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(A_66,k3_xboole_0(B_67,C_68))
      | ~ r1_tarski(A_66,C_68)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_139,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_131,c_32])).

tff(c_166,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_169,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_172,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4,c_169])).

tff(c_175,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_172])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_175])).

tff(c_183,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_187,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_183])).

tff(c_190,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112,c_187])).

tff(c_197,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_190])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.21  
% 2.06/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.21  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.06/1.21  
% 2.06/1.21  %Foreground sorts:
% 2.06/1.21  
% 2.06/1.21  
% 2.06/1.21  %Background operators:
% 2.06/1.21  
% 2.06/1.21  
% 2.06/1.21  %Foreground operators:
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.06/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.21  
% 2.06/1.23  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 2.06/1.23  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.06/1.23  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.06/1.23  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.06/1.23  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.23  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.06/1.23  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.06/1.23  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.06/1.23  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.06/1.23  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.23  tff(c_12, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.23  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k3_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.23  tff(c_10, plain, (![A_11, B_12, C_13]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13)), k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.23  tff(c_101, plain, (![A_56, B_57, C_58]: (r1_tarski(k3_xboole_0(A_56, k2_xboole_0(B_57, C_58)), k2_xboole_0(B_57, C_58)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.06/1.23  tff(c_107, plain, (![A_56, A_14, B_15]: (r1_tarski(k3_xboole_0(A_56, A_14), k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_101])).
% 2.06/1.23  tff(c_124, plain, (![A_62, A_63]: (r1_tarski(k3_xboole_0(A_62, A_63), A_63))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_107])).
% 2.06/1.23  tff(c_24, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.23  tff(c_81, plain, (![B_48, A_49]: (v1_relat_1(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.23  tff(c_85, plain, (![A_25, B_26]: (v1_relat_1(A_25) | ~v1_relat_1(B_26) | ~r1_tarski(A_25, B_26))), inference(resolution, [status(thm)], [c_24, c_81])).
% 2.06/1.23  tff(c_128, plain, (![A_62, A_63]: (v1_relat_1(k3_xboole_0(A_62, A_63)) | ~v1_relat_1(A_63))), inference(resolution, [status(thm)], [c_124, c_85])).
% 2.06/1.23  tff(c_112, plain, (![A_56, A_14]: (r1_tarski(k3_xboole_0(A_56, A_14), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_107])).
% 2.06/1.23  tff(c_28, plain, (![A_30, B_32]: (r1_tarski(k2_relat_1(A_30), k2_relat_1(B_32)) | ~r1_tarski(A_30, B_32) | ~v1_relat_1(B_32) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.23  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.23  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.23  tff(c_131, plain, (![A_66, B_67, C_68]: (r1_tarski(A_66, k3_xboole_0(B_67, C_68)) | ~r1_tarski(A_66, C_68) | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.23  tff(c_32, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.23  tff(c_139, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_131, c_32])).
% 2.06/1.23  tff(c_166, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.06/1.23  tff(c_169, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_166])).
% 2.06/1.23  tff(c_172, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4, c_169])).
% 2.06/1.23  tff(c_175, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_128, c_172])).
% 2.06/1.23  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_175])).
% 2.06/1.23  tff(c_183, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_139])).
% 2.06/1.23  tff(c_187, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_183])).
% 2.06/1.23  tff(c_190, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_112, c_187])).
% 2.06/1.23  tff(c_197, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_128, c_190])).
% 2.06/1.23  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_197])).
% 2.06/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 34
% 2.06/1.23  #Fact    : 0
% 2.06/1.23  #Define  : 0
% 2.06/1.23  #Split   : 1
% 2.06/1.23  #Chain   : 0
% 2.06/1.23  #Close   : 0
% 2.06/1.23  
% 2.06/1.23  Ordering : KBO
% 2.06/1.23  
% 2.06/1.23  Simplification rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Subsume      : 3
% 2.06/1.23  #Demod        : 11
% 2.06/1.23  #Tautology    : 17
% 2.06/1.23  #SimpNegUnit  : 0
% 2.06/1.23  #BackRed      : 0
% 2.06/1.23  
% 2.06/1.23  #Partial instantiations: 0
% 2.06/1.23  #Strategies tried      : 1
% 2.06/1.23  
% 2.06/1.23  Timing (in seconds)
% 2.06/1.23  ----------------------
% 2.06/1.23  Preprocessing        : 0.30
% 2.06/1.23  Parsing              : 0.16
% 2.06/1.23  CNF conversion       : 0.02
% 2.06/1.23  Main loop            : 0.16
% 2.06/1.23  Inferencing          : 0.06
% 2.06/1.23  Reduction            : 0.05
% 2.06/1.23  Demodulation         : 0.04
% 2.06/1.23  BG Simplification    : 0.01
% 2.06/1.23  Subsumption          : 0.03
% 2.06/1.23  Abstraction          : 0.01
% 2.06/1.23  MUC search           : 0.00
% 2.06/1.23  Cooper               : 0.00
% 2.06/1.23  Total                : 0.49
% 2.06/1.23  Index Insertion      : 0.00
% 2.06/1.23  Index Deletion       : 0.00
% 2.06/1.23  Index Matching       : 0.00
% 2.06/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

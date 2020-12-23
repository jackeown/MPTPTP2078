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
% DateTime   : Thu Dec  3 09:58:43 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 102 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 177 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(A_44,B_45)
      | ~ r1_tarski(A_44,k3_xboole_0(B_45,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [B_47,C_48] : r1_tarski(k3_xboole_0(B_47,C_48),B_47) ),
    inference(resolution,[status(thm)],[c_8,c_100])).

tff(c_121,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_145,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_150,plain,(
    ! [A_53,B_54] :
      ( v1_relat_1(A_53)
      | ~ v1_relat_1(B_54)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_20,c_145])).

tff(c_160,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_121,c_150])).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_24,plain,(
    ! [C_26,A_20,B_24] :
      ( r1_tarski(k5_relat_1(C_26,A_20),k5_relat_1(C_26,B_24))
      | ~ r1_tarski(A_20,B_24)
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_111,plain,(
    ! [B_45,C_46] : r1_tarski(k3_xboole_0(B_45,C_46),B_45) ),
    inference(resolution,[status(thm)],[c_8,c_100])).

tff(c_177,plain,(
    ! [A_59,B_60,C_61] :
      ( r1_tarski(A_59,k3_xboole_0(B_60,C_61))
      | ~ r1_tarski(A_59,C_61)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k5_relat_1('#skF_1','#skF_3'),k5_relat_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_26])).

tff(c_198,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_177,c_34])).

tff(c_295,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_426,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_295])).

tff(c_429,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_111,c_426])).

tff(c_432,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_429])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_432])).

tff(c_440,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_557,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_440])).

tff(c_560,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_121,c_557])).

tff(c_563,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_160,c_560])).

tff(c_570,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.36  
% 2.41/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.37  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.41/1.37  
% 2.41/1.37  %Foreground sorts:
% 2.41/1.37  
% 2.41/1.37  
% 2.41/1.37  %Background operators:
% 2.41/1.37  
% 2.41/1.37  
% 2.41/1.37  %Foreground operators:
% 2.41/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.37  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.41/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.37  
% 2.41/1.38  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 2.41/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.41/1.38  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.41/1.38  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.41/1.38  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.41/1.38  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.41/1.38  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 2.41/1.38  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.41/1.38  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.38  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.38  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.38  tff(c_100, plain, (![A_44, B_45, C_46]: (r1_tarski(A_44, B_45) | ~r1_tarski(A_44, k3_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.38  tff(c_112, plain, (![B_47, C_48]: (r1_tarski(k3_xboole_0(B_47, C_48), B_47))), inference(resolution, [status(thm)], [c_8, c_100])).
% 2.41/1.38  tff(c_121, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 2.41/1.38  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.41/1.38  tff(c_145, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.38  tff(c_150, plain, (![A_53, B_54]: (v1_relat_1(A_53) | ~v1_relat_1(B_54) | ~r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_20, c_145])).
% 2.41/1.38  tff(c_160, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_121, c_150])).
% 2.41/1.38  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.38  tff(c_24, plain, (![C_26, A_20, B_24]: (r1_tarski(k5_relat_1(C_26, A_20), k5_relat_1(C_26, B_24)) | ~r1_tarski(A_20, B_24) | ~v1_relat_1(C_26) | ~v1_relat_1(B_24) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.41/1.38  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.38  tff(c_111, plain, (![B_45, C_46]: (r1_tarski(k3_xboole_0(B_45, C_46), B_45))), inference(resolution, [status(thm)], [c_8, c_100])).
% 2.41/1.38  tff(c_177, plain, (![A_59, B_60, C_61]: (r1_tarski(A_59, k3_xboole_0(B_60, C_61)) | ~r1_tarski(A_59, C_61) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.38  tff(c_26, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.41/1.38  tff(c_34, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_3'), k5_relat_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_26])).
% 2.41/1.38  tff(c_198, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_177, c_34])).
% 2.41/1.38  tff(c_295, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_198])).
% 2.41/1.38  tff(c_426, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_295])).
% 2.41/1.38  tff(c_429, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_111, c_426])).
% 2.41/1.38  tff(c_432, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_160, c_429])).
% 2.41/1.38  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_432])).
% 2.41/1.38  tff(c_440, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_198])).
% 2.41/1.38  tff(c_557, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_440])).
% 2.41/1.38  tff(c_560, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_121, c_557])).
% 2.41/1.38  tff(c_563, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_160, c_560])).
% 2.41/1.38  tff(c_570, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_563])).
% 2.41/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.38  
% 2.41/1.38  Inference rules
% 2.41/1.38  ----------------------
% 2.41/1.38  #Ref     : 0
% 2.41/1.38  #Sup     : 122
% 2.41/1.38  #Fact    : 0
% 2.41/1.38  #Define  : 0
% 2.41/1.38  #Split   : 1
% 2.41/1.38  #Chain   : 0
% 2.41/1.38  #Close   : 0
% 2.41/1.38  
% 2.41/1.38  Ordering : KBO
% 2.41/1.38  
% 2.41/1.38  Simplification rules
% 2.41/1.38  ----------------------
% 2.41/1.38  #Subsume      : 18
% 2.41/1.38  #Demod        : 42
% 2.41/1.38  #Tautology    : 49
% 2.41/1.38  #SimpNegUnit  : 0
% 2.41/1.38  #BackRed      : 0
% 2.41/1.38  
% 2.41/1.38  #Partial instantiations: 0
% 2.41/1.38  #Strategies tried      : 1
% 2.41/1.38  
% 2.41/1.38  Timing (in seconds)
% 2.41/1.38  ----------------------
% 2.41/1.38  Preprocessing        : 0.33
% 2.41/1.38  Parsing              : 0.18
% 2.41/1.38  CNF conversion       : 0.02
% 2.41/1.38  Main loop            : 0.27
% 2.41/1.38  Inferencing          : 0.09
% 2.41/1.38  Reduction            : 0.09
% 2.41/1.38  Demodulation         : 0.08
% 2.41/1.38  BG Simplification    : 0.01
% 2.41/1.38  Subsumption          : 0.05
% 2.41/1.38  Abstraction          : 0.02
% 2.41/1.38  MUC search           : 0.00
% 2.41/1.38  Cooper               : 0.00
% 2.41/1.38  Total                : 0.63
% 2.41/1.38  Index Insertion      : 0.00
% 2.41/1.38  Index Deletion       : 0.00
% 2.41/1.38  Index Matching       : 0.00
% 2.41/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

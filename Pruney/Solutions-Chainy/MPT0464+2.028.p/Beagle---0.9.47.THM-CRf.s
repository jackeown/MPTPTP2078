%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:46 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 104 expanded)
%              Number of leaves         :   30 (  50 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 157 expanded)
%              Number of equality atoms :    4 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_14,B_15] : k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,C_10)) = k3_xboole_0(A_8,k2_xboole_0(B_9,C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] : r1_tarski(k2_xboole_0(k3_xboole_0(A_11,B_12),k3_xboole_0(A_11,C_13)),k2_xboole_0(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_70,B_71,C_72] : r1_tarski(k3_xboole_0(A_70,k2_xboole_0(B_71,C_72)),k2_xboole_0(B_71,C_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_118,plain,(
    ! [A_70,A_14,B_15] : r1_tarski(k3_xboole_0(A_70,A_14),k2_xboole_0(k3_xboole_0(A_14,B_15),k4_xboole_0(A_14,B_15))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_112])).

tff(c_126,plain,(
    ! [A_73,A_74] : r1_tarski(k3_xboole_0(A_73,A_74),A_74) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_92,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    ! [A_29,B_30] :
      ( v1_relat_1(A_29)
      | ~ v1_relat_1(B_30)
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_26,c_92])).

tff(c_130,plain,(
    ! [A_73,A_74] :
      ( v1_relat_1(k3_xboole_0(A_73,A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_126,c_96])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_123,plain,(
    ! [A_70,A_14] : r1_tarski(k3_xboole_0(A_70,A_14),A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_118])).

tff(c_30,plain,(
    ! [C_40,A_34,B_38] :
      ( r1_tarski(k5_relat_1(C_40,A_34),k5_relat_1(C_40,B_38))
      | ~ r1_tarski(A_34,B_38)
      | ~ v1_relat_1(C_40)
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ! [A_81,B_82,C_83] :
      ( r1_tarski(A_81,k3_xboole_0(B_82,C_83))
      | ~ r1_tarski(A_81,C_83)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_32,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_150,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_142,c_32])).

tff(c_173,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_176,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_173])).

tff(c_179,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_4,c_176])).

tff(c_182,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_179])).

tff(c_189,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_182])).

tff(c_190,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_194,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_190])).

tff(c_197,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38,c_123,c_194])).

tff(c_200,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_130,c_197])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_200])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 1.96/1.21  
% 1.96/1.21  %Foreground sorts:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Background operators:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Foreground operators:
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.21  
% 1.96/1.22  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 1.96/1.22  tff(f_41, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.96/1.22  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 1.96/1.22  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 1.96/1.22  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.96/1.22  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.96/1.22  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 1.96/1.22  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.96/1.22  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 1.96/1.22  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.96/1.22  tff(c_12, plain, (![A_14, B_15]: (k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.96/1.22  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, C_10))=k3_xboole_0(A_8, k2_xboole_0(B_9, C_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.22  tff(c_10, plain, (![A_11, B_12, C_13]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_11, B_12), k3_xboole_0(A_11, C_13)), k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.22  tff(c_112, plain, (![A_70, B_71, C_72]: (r1_tarski(k3_xboole_0(A_70, k2_xboole_0(B_71, C_72)), k2_xboole_0(B_71, C_72)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 1.96/1.22  tff(c_118, plain, (![A_70, A_14, B_15]: (r1_tarski(k3_xboole_0(A_70, A_14), k2_xboole_0(k3_xboole_0(A_14, B_15), k4_xboole_0(A_14, B_15))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_112])).
% 1.96/1.22  tff(c_126, plain, (![A_73, A_74]: (r1_tarski(k3_xboole_0(A_73, A_74), A_74))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118])).
% 1.96/1.22  tff(c_26, plain, (![A_29, B_30]: (m1_subset_1(A_29, k1_zfmisc_1(B_30)) | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.22  tff(c_92, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.22  tff(c_96, plain, (![A_29, B_30]: (v1_relat_1(A_29) | ~v1_relat_1(B_30) | ~r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_26, c_92])).
% 1.96/1.22  tff(c_130, plain, (![A_73, A_74]: (v1_relat_1(k3_xboole_0(A_73, A_74)) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_126, c_96])).
% 1.96/1.22  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.96/1.22  tff(c_123, plain, (![A_70, A_14]: (r1_tarski(k3_xboole_0(A_70, A_14), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_118])).
% 1.96/1.22  tff(c_30, plain, (![C_40, A_34, B_38]: (r1_tarski(k5_relat_1(C_40, A_34), k5_relat_1(C_40, B_38)) | ~r1_tarski(A_34, B_38) | ~v1_relat_1(C_40) | ~v1_relat_1(B_38) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.22  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.96/1.22  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.22  tff(c_142, plain, (![A_81, B_82, C_83]: (r1_tarski(A_81, k3_xboole_0(B_82, C_83)) | ~r1_tarski(A_81, C_83) | ~r1_tarski(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.22  tff(c_32, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 1.96/1.22  tff(c_150, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_142, c_32])).
% 1.96/1.22  tff(c_173, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_150])).
% 1.96/1.22  tff(c_176, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_173])).
% 1.96/1.22  tff(c_179, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_4, c_176])).
% 1.96/1.22  tff(c_182, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_179])).
% 1.96/1.22  tff(c_189, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_182])).
% 1.96/1.22  tff(c_190, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_150])).
% 1.96/1.22  tff(c_194, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_190])).
% 1.96/1.22  tff(c_197, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38, c_123, c_194])).
% 1.96/1.22  tff(c_200, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_130, c_197])).
% 1.96/1.22  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_200])).
% 1.96/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  Inference rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Ref     : 0
% 1.96/1.22  #Sup     : 34
% 1.96/1.22  #Fact    : 0
% 1.96/1.22  #Define  : 0
% 1.96/1.22  #Split   : 1
% 1.96/1.22  #Chain   : 0
% 1.96/1.22  #Close   : 0
% 1.96/1.22  
% 1.96/1.22  Ordering : KBO
% 1.96/1.22  
% 1.96/1.22  Simplification rules
% 1.96/1.22  ----------------------
% 1.96/1.22  #Subsume      : 3
% 1.96/1.22  #Demod        : 13
% 1.96/1.22  #Tautology    : 19
% 1.96/1.22  #SimpNegUnit  : 0
% 1.96/1.22  #BackRed      : 0
% 1.96/1.22  
% 1.96/1.22  #Partial instantiations: 0
% 1.96/1.22  #Strategies tried      : 1
% 1.96/1.22  
% 1.96/1.22  Timing (in seconds)
% 1.96/1.22  ----------------------
% 1.96/1.23  Preprocessing        : 0.30
% 1.96/1.23  Parsing              : 0.16
% 1.96/1.23  CNF conversion       : 0.02
% 1.96/1.23  Main loop            : 0.17
% 1.96/1.23  Inferencing          : 0.06
% 1.96/1.23  Reduction            : 0.05
% 1.96/1.23  Demodulation         : 0.04
% 1.96/1.23  BG Simplification    : 0.01
% 1.96/1.23  Subsumption          : 0.03
% 1.96/1.23  Abstraction          : 0.01
% 1.96/1.23  MUC search           : 0.00
% 1.96/1.23  Cooper               : 0.00
% 1.96/1.23  Total                : 0.50
% 1.96/1.23  Index Insertion      : 0.00
% 1.96/1.23  Index Deletion       : 0.00
% 1.96/1.23  Index Matching       : 0.00
% 1.96/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:52 EST 2020

% Result     : Theorem 8.39s
% Output     : CNFRefutation 8.67s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 124 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ( v2_tops_2(B,A)
                 => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tops_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v2_tops_2(C,A) )
               => v2_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tops_2)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_200,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [B_50] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_50,'#skF_3') = k3_xboole_0(B_50,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_200])).

tff(c_18,plain,(
    ~ v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_364,plain,(
    ~ v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_18])).

tff(c_20,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_365,plain,(
    ! [B_64] : k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),B_64,'#skF_3') = k3_xboole_0(B_64,'#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_200])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k9_subset_1(A_9,B_10,C_11),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_371,plain,(
    ! [B_64] :
      ( m1_subset_1(k3_xboole_0(B_64,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_10])).

tff(c_377,plain,(
    ! [B_64] : m1_subset_1(k3_xboole_0(B_64,'#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_371])).

tff(c_8,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_36,B_37] :
      ( k2_xboole_0(A_36,B_37) = B_37
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_38] : k2_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    ! [A_38] : k2_xboole_0(A_38,k1_xboole_0) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_2])).

tff(c_85,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : r1_tarski(k3_xboole_0(A_5,B_6),k2_xboole_0(A_5,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_272,plain,(
    ! [B_55,A_56,C_57] :
      ( v2_tops_2(B_55,A_56)
      | ~ v2_tops_2(C_57,A_56)
      | ~ r1_tarski(B_55,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56))))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1096,plain,(
    ! [A_114,B_115,A_116,C_117] :
      ( v2_tops_2(k3_xboole_0(A_114,B_115),A_116)
      | ~ v2_tops_2(k2_xboole_0(A_114,C_117),A_116)
      | ~ m1_subset_1(k2_xboole_0(A_114,C_117),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116))))
      | ~ m1_subset_1(k3_xboole_0(A_114,B_115),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116))))
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_272])).

tff(c_2881,plain,(
    ! [B_189,B_190,A_191,A_192] :
      ( v2_tops_2(k3_xboole_0(B_189,B_190),A_191)
      | ~ v2_tops_2(k2_xboole_0(B_189,A_192),A_191)
      | ~ m1_subset_1(k2_xboole_0(A_192,B_189),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ m1_subset_1(k3_xboole_0(B_189,B_190),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ l1_pre_topc(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1096])).

tff(c_2915,plain,(
    ! [A_8,B_190,A_191] :
      ( v2_tops_2(k3_xboole_0(A_8,B_190),A_191)
      | ~ v2_tops_2(k2_xboole_0(A_8,k1_xboole_0),A_191)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ m1_subset_1(k3_xboole_0(A_8,B_190),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191))))
      | ~ l1_pre_topc(A_191) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_2881])).

tff(c_9216,plain,(
    ! [A_315,B_316,A_317] :
      ( v2_tops_2(k3_xboole_0(A_315,B_316),A_317)
      | ~ v2_tops_2(A_315,A_317)
      | ~ m1_subset_1(A_315,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_317))))
      | ~ m1_subset_1(k3_xboole_0(A_315,B_316),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_317))))
      | ~ l1_pre_topc(A_317) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_2915])).

tff(c_9243,plain,(
    ! [B_64] :
      ( v2_tops_2(k3_xboole_0(B_64,'#skF_3'),'#skF_1')
      | ~ v2_tops_2(B_64,'#skF_1')
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_377,c_9216])).

tff(c_9284,plain,(
    ! [B_318] :
      ( v2_tops_2(k3_xboole_0(B_318,'#skF_3'),'#skF_1')
      | ~ v2_tops_2(B_318,'#skF_1')
      | ~ m1_subset_1(B_318,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_9243])).

tff(c_9327,plain,
    ( v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_tops_2('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_9284])).

tff(c_9345,plain,(
    v2_tops_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_9327])).

tff(c_9347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_364,c_9345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.39/3.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/3.28  
% 8.39/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.39/3.28  %$ v2_tops_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 8.39/3.28  
% 8.39/3.28  %Foreground sorts:
% 8.39/3.28  
% 8.39/3.28  
% 8.39/3.28  %Background operators:
% 8.39/3.28  
% 8.39/3.28  
% 8.39/3.28  %Foreground operators:
% 8.39/3.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.39/3.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.39/3.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.39/3.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.39/3.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.39/3.28  tff('#skF_2', type, '#skF_2': $i).
% 8.39/3.28  tff('#skF_3', type, '#skF_3': $i).
% 8.39/3.28  tff('#skF_1', type, '#skF_1': $i).
% 8.39/3.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.39/3.28  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 8.39/3.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.39/3.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.39/3.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.39/3.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.39/3.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.39/3.28  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 8.39/3.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.39/3.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 8.39/3.28  
% 8.67/3.29  tff(f_72, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) => v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tops_2)).
% 8.67/3.29  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 8.67/3.29  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 8.67/3.29  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.67/3.29  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.67/3.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.67/3.29  tff(f_33, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_xboole_1)).
% 8.67/3.29  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v2_tops_2(C, A)) => v2_tops_2(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tops_2)).
% 8.67/3.29  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.67/3.29  tff(c_200, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.67/3.29  tff(c_208, plain, (![B_50]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_50, '#skF_3')=k3_xboole_0(B_50, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_200])).
% 8.67/3.29  tff(c_18, plain, (~v2_tops_2(k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.67/3.29  tff(c_364, plain, (~v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_208, c_18])).
% 8.67/3.29  tff(c_20, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.67/3.29  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.67/3.29  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.67/3.29  tff(c_365, plain, (![B_64]: (k9_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), B_64, '#skF_3')=k3_xboole_0(B_64, '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_200])).
% 8.67/3.29  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k9_subset_1(A_9, B_10, C_11), k1_zfmisc_1(A_9)) | ~m1_subset_1(C_11, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.67/3.29  tff(c_371, plain, (![B_64]: (m1_subset_1(k3_xboole_0(B_64, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_365, c_10])).
% 8.67/3.29  tff(c_377, plain, (![B_64]: (m1_subset_1(k3_xboole_0(B_64, '#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_371])).
% 8.67/3.29  tff(c_8, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.67/3.29  tff(c_77, plain, (![A_36, B_37]: (k2_xboole_0(A_36, B_37)=B_37 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.67/3.29  tff(c_86, plain, (![A_38]: (k2_xboole_0(k1_xboole_0, A_38)=A_38)), inference(resolution, [status(thm)], [c_8, c_77])).
% 8.67/3.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.67/3.29  tff(c_95, plain, (![A_38]: (k2_xboole_0(A_38, k1_xboole_0)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_86, c_2])).
% 8.67/3.29  tff(c_85, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_77])).
% 8.67/3.29  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k3_xboole_0(A_5, B_6), k2_xboole_0(A_5, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.67/3.29  tff(c_272, plain, (![B_55, A_56, C_57]: (v2_tops_2(B_55, A_56) | ~v2_tops_2(C_57, A_56) | ~r1_tarski(B_55, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_56)))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.67/3.29  tff(c_1096, plain, (![A_114, B_115, A_116, C_117]: (v2_tops_2(k3_xboole_0(A_114, B_115), A_116) | ~v2_tops_2(k2_xboole_0(A_114, C_117), A_116) | ~m1_subset_1(k2_xboole_0(A_114, C_117), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116)))) | ~m1_subset_1(k3_xboole_0(A_114, B_115), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_116)))) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_6, c_272])).
% 8.67/3.29  tff(c_2881, plain, (![B_189, B_190, A_191, A_192]: (v2_tops_2(k3_xboole_0(B_189, B_190), A_191) | ~v2_tops_2(k2_xboole_0(B_189, A_192), A_191) | ~m1_subset_1(k2_xboole_0(A_192, B_189), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~m1_subset_1(k3_xboole_0(B_189, B_190), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~l1_pre_topc(A_191))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1096])).
% 8.67/3.29  tff(c_2915, plain, (![A_8, B_190, A_191]: (v2_tops_2(k3_xboole_0(A_8, B_190), A_191) | ~v2_tops_2(k2_xboole_0(A_8, k1_xboole_0), A_191) | ~m1_subset_1(A_8, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~m1_subset_1(k3_xboole_0(A_8, B_190), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_191)))) | ~l1_pre_topc(A_191))), inference(superposition, [status(thm), theory('equality')], [c_85, c_2881])).
% 8.67/3.29  tff(c_9216, plain, (![A_315, B_316, A_317]: (v2_tops_2(k3_xboole_0(A_315, B_316), A_317) | ~v2_tops_2(A_315, A_317) | ~m1_subset_1(A_315, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_317)))) | ~m1_subset_1(k3_xboole_0(A_315, B_316), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_317)))) | ~l1_pre_topc(A_317))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_2915])).
% 8.67/3.29  tff(c_9243, plain, (![B_64]: (v2_tops_2(k3_xboole_0(B_64, '#skF_3'), '#skF_1') | ~v2_tops_2(B_64, '#skF_1') | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_377, c_9216])).
% 8.67/3.29  tff(c_9284, plain, (![B_318]: (v2_tops_2(k3_xboole_0(B_318, '#skF_3'), '#skF_1') | ~v2_tops_2(B_318, '#skF_1') | ~m1_subset_1(B_318, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_9243])).
% 8.67/3.29  tff(c_9327, plain, (v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_9284])).
% 8.67/3.29  tff(c_9345, plain, (v2_tops_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_9327])).
% 8.67/3.29  tff(c_9347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_364, c_9345])).
% 8.67/3.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.67/3.29  
% 8.67/3.29  Inference rules
% 8.67/3.29  ----------------------
% 8.67/3.29  #Ref     : 0
% 8.67/3.29  #Sup     : 2344
% 8.67/3.29  #Fact    : 0
% 8.67/3.29  #Define  : 0
% 8.67/3.29  #Split   : 0
% 8.67/3.29  #Chain   : 0
% 8.67/3.29  #Close   : 0
% 8.67/3.29  
% 8.67/3.29  Ordering : KBO
% 8.67/3.29  
% 8.67/3.29  Simplification rules
% 8.67/3.29  ----------------------
% 8.67/3.29  #Subsume      : 166
% 8.67/3.29  #Demod        : 3676
% 8.67/3.29  #Tautology    : 1365
% 8.67/3.29  #SimpNegUnit  : 1
% 8.67/3.29  #BackRed      : 4
% 8.67/3.29  
% 8.67/3.29  #Partial instantiations: 0
% 8.67/3.29  #Strategies tried      : 1
% 8.67/3.29  
% 8.67/3.29  Timing (in seconds)
% 8.67/3.29  ----------------------
% 8.67/3.29  Preprocessing        : 0.31
% 8.67/3.29  Parsing              : 0.16
% 8.67/3.29  CNF conversion       : 0.02
% 8.67/3.29  Main loop            : 2.21
% 8.67/3.29  Inferencing          : 0.51
% 8.67/3.29  Reduction            : 1.27
% 8.67/3.29  Demodulation         : 1.13
% 8.67/3.29  BG Simplification    : 0.06
% 8.67/3.29  Subsumption          : 0.28
% 8.67/3.29  Abstraction          : 0.14
% 8.67/3.29  MUC search           : 0.00
% 8.67/3.29  Cooper               : 0.00
% 8.67/3.29  Total                : 2.55
% 8.67/3.29  Index Insertion      : 0.00
% 8.67/3.29  Index Deletion       : 0.00
% 8.67/3.29  Index Matching       : 0.00
% 8.67/3.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

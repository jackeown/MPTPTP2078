%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:37 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   60 (  86 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 127 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => r1_tarski(k7_subset_1(u1_struct_0(A),k5_setfam_1(u1_struct_0(A),B),k5_setfam_1(u1_struct_0(A),C)),k5_setfam_1(u1_struct_0(A),k7_subset_1(k1_zfmisc_1(u1_struct_0(A)),B,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tops_2)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( r1_tarski(C,B)
             => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_31,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_37,B_36] : r1_tarski(A_37,k2_xboole_0(B_36,A_37)) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_10])).

tff(c_119,plain,(
    ! [A_46,B_47] : k2_xboole_0(k3_tarski(A_46),k3_tarski(B_47)) = k3_tarski(k2_xboole_0(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [B_47,A_46] : r1_tarski(k3_tarski(B_47),k3_tarski(k2_xboole_0(A_46,B_47))) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_46])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_tarski(A_12),k3_tarski(B_13)) = k3_tarski(k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(k4_xboole_0(A_7,B_8),C_9)
      | ~ r1_tarski(A_7,k2_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_538,plain,(
    ! [C_77,A_78,B_79] :
      ( m1_subset_1(C_77,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ r1_tarski(C_77,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78))))
      | ~ l1_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1370,plain,(
    ! [A_124,B_125,A_126,C_127] :
      ( m1_subset_1(k4_xboole_0(A_124,B_125),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126))))
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126))))
      | ~ l1_struct_0(A_126)
      | ~ r1_tarski(A_124,k2_xboole_0(B_125,C_127)) ) ),
    inference(resolution,[status(thm)],[c_8,c_538])).

tff(c_1379,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1(k4_xboole_0(A_124,B_125),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_124,k2_xboole_0(B_125,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_26,c_1370])).

tff(c_1440,plain,(
    ! [A_132,B_133] :
      ( m1_subset_1(k4_xboole_0(A_132,B_133),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_132,k2_xboole_0(B_133,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1379])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( k5_setfam_1(A_19,B_20) = k3_tarski(B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(A_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1497,plain,(
    ! [A_138,B_139] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0(A_138,B_139)) = k3_tarski(k4_xboole_0(A_138,B_139))
      | ~ r1_tarski(A_138,k2_xboole_0(B_139,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1440,c_18])).

tff(c_184,plain,(
    ! [A_55,B_56] :
      ( k5_setfam_1(A_55,B_56) = k3_tarski(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_192,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_184])).

tff(c_461,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k5_setfam_1(A_70,B_71),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k1_zfmisc_1(A_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_470,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_461])).

tff(c_477,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_470])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( k7_subset_1(A_14,B_15,C_16) = k4_xboole_0(B_15,C_16)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_482,plain,(
    ! [C_16] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_16) = k4_xboole_0(k3_tarski('#skF_2'),C_16) ),
    inference(resolution,[status(thm)],[c_477,c_14])).

tff(c_370,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_subset_1(A_61,B_62,C_63) = k4_xboole_0(B_62,C_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_376,plain,(
    ! [C_63] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_63) = k4_xboole_0('#skF_2',C_63) ),
    inference(resolution,[status(thm)],[c_26,c_370])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_191,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_184])).

tff(c_22,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_193,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_22])).

tff(c_396,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_192,c_193])).

tff(c_487,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_396])).

tff(c_629,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_8,c_487])).

tff(c_1503,plain,
    ( ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_629])).

tff(c_1516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_131,c_6,c_12,c_1503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.71  
% 3.82/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.72  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.82/1.72  
% 3.82/1.72  %Foreground sorts:
% 3.82/1.72  
% 3.82/1.72  
% 3.82/1.72  %Background operators:
% 3.82/1.72  
% 3.82/1.72  
% 3.82/1.72  %Foreground operators:
% 3.82/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.82/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.72  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.82/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.82/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.82/1.72  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.82/1.72  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.82/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.82/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.82/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.82/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.82/1.72  
% 3.82/1.73  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.82/1.73  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.82/1.73  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 3.82/1.73  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.82/1.73  tff(f_72, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 3.82/1.73  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.82/1.73  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_tops_2)).
% 3.82/1.73  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.82/1.73  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.82/1.73  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.82/1.73  tff(c_31, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/1.73  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.73  tff(c_46, plain, (![A_37, B_36]: (r1_tarski(A_37, k2_xboole_0(B_36, A_37)))), inference(superposition, [status(thm), theory('equality')], [c_31, c_10])).
% 3.82/1.73  tff(c_119, plain, (![A_46, B_47]: (k2_xboole_0(k3_tarski(A_46), k3_tarski(B_47))=k3_tarski(k2_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.73  tff(c_131, plain, (![B_47, A_46]: (r1_tarski(k3_tarski(B_47), k3_tarski(k2_xboole_0(A_46, B_47))))), inference(superposition, [status(thm), theory('equality')], [c_119, c_46])).
% 3.82/1.73  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.73  tff(c_12, plain, (![A_12, B_13]: (k2_xboole_0(k3_tarski(A_12), k3_tarski(B_13))=k3_tarski(k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.73  tff(c_28, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.73  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.73  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski(k4_xboole_0(A_7, B_8), C_9) | ~r1_tarski(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.82/1.73  tff(c_538, plain, (![C_77, A_78, B_79]: (m1_subset_1(C_77, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78)))) | ~r1_tarski(C_77, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_78)))) | ~l1_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.82/1.73  tff(c_1370, plain, (![A_124, B_125, A_126, C_127]: (m1_subset_1(k4_xboole_0(A_124, B_125), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126)))) | ~m1_subset_1(C_127, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126)))) | ~l1_struct_0(A_126) | ~r1_tarski(A_124, k2_xboole_0(B_125, C_127)))), inference(resolution, [status(thm)], [c_8, c_538])).
% 3.82/1.73  tff(c_1379, plain, (![A_124, B_125]: (m1_subset_1(k4_xboole_0(A_124, B_125), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_124, k2_xboole_0(B_125, '#skF_2')))), inference(resolution, [status(thm)], [c_26, c_1370])).
% 3.82/1.73  tff(c_1440, plain, (![A_132, B_133]: (m1_subset_1(k4_xboole_0(A_132, B_133), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_132, k2_xboole_0(B_133, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1379])).
% 3.82/1.73  tff(c_18, plain, (![A_19, B_20]: (k5_setfam_1(A_19, B_20)=k3_tarski(B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(A_19))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/1.73  tff(c_1497, plain, (![A_138, B_139]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0(A_138, B_139))=k3_tarski(k4_xboole_0(A_138, B_139)) | ~r1_tarski(A_138, k2_xboole_0(B_139, '#skF_2')))), inference(resolution, [status(thm)], [c_1440, c_18])).
% 3.82/1.73  tff(c_184, plain, (![A_55, B_56]: (k5_setfam_1(A_55, B_56)=k3_tarski(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/1.73  tff(c_192, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_26, c_184])).
% 3.82/1.73  tff(c_461, plain, (![A_70, B_71]: (m1_subset_1(k5_setfam_1(A_70, B_71), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, k1_zfmisc_1(k1_zfmisc_1(A_70))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.73  tff(c_470, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_192, c_461])).
% 3.82/1.73  tff(c_477, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_470])).
% 3.82/1.73  tff(c_14, plain, (![A_14, B_15, C_16]: (k7_subset_1(A_14, B_15, C_16)=k4_xboole_0(B_15, C_16) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/1.73  tff(c_482, plain, (![C_16]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_16)=k4_xboole_0(k3_tarski('#skF_2'), C_16))), inference(resolution, [status(thm)], [c_477, c_14])).
% 3.82/1.73  tff(c_370, plain, (![A_61, B_62, C_63]: (k7_subset_1(A_61, B_62, C_63)=k4_xboole_0(B_62, C_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/1.73  tff(c_376, plain, (![C_63]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_63)=k4_xboole_0('#skF_2', C_63))), inference(resolution, [status(thm)], [c_26, c_370])).
% 3.82/1.73  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.73  tff(c_191, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_24, c_184])).
% 3.82/1.73  tff(c_22, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/1.73  tff(c_193, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_22])).
% 3.82/1.73  tff(c_396, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_192, c_193])).
% 3.82/1.73  tff(c_487, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_482, c_396])).
% 3.82/1.73  tff(c_629, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_8, c_487])).
% 3.82/1.73  tff(c_1503, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1497, c_629])).
% 3.82/1.73  tff(c_1516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_131, c_6, c_12, c_1503])).
% 3.82/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.73  
% 3.82/1.73  Inference rules
% 3.82/1.73  ----------------------
% 3.82/1.73  #Ref     : 0
% 3.82/1.73  #Sup     : 403
% 3.82/1.73  #Fact    : 0
% 3.82/1.73  #Define  : 0
% 3.82/1.73  #Split   : 0
% 3.82/1.73  #Chain   : 0
% 3.82/1.73  #Close   : 0
% 3.82/1.73  
% 3.82/1.73  Ordering : KBO
% 3.82/1.73  
% 3.82/1.73  Simplification rules
% 3.82/1.73  ----------------------
% 3.82/1.73  #Subsume      : 3
% 3.82/1.73  #Demod        : 172
% 3.82/1.73  #Tautology    : 189
% 3.82/1.73  #SimpNegUnit  : 0
% 3.82/1.73  #BackRed      : 2
% 3.82/1.73  
% 3.82/1.73  #Partial instantiations: 0
% 3.82/1.73  #Strategies tried      : 1
% 3.82/1.73  
% 3.82/1.73  Timing (in seconds)
% 3.82/1.73  ----------------------
% 3.82/1.73  Preprocessing        : 0.33
% 3.82/1.73  Parsing              : 0.17
% 3.82/1.73  CNF conversion       : 0.02
% 3.82/1.73  Main loop            : 0.55
% 3.82/1.73  Inferencing          : 0.15
% 3.82/1.73  Reduction            : 0.25
% 3.82/1.73  Demodulation         : 0.21
% 3.82/1.73  BG Simplification    : 0.02
% 3.82/1.73  Subsumption          : 0.09
% 3.82/1.73  Abstraction          : 0.03
% 3.82/1.73  MUC search           : 0.00
% 3.82/1.73  Cooper               : 0.00
% 3.82/1.73  Total                : 0.91
% 3.82/1.73  Index Insertion      : 0.00
% 3.82/1.73  Index Deletion       : 0.00
% 3.82/1.73  Index Matching       : 0.00
% 3.82/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

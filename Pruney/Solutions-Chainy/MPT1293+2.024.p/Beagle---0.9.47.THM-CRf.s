%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:38 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   60 (  87 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 132 expanded)
%              Number of equality atoms :   14 (  24 expanded)
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
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_xboole_0(A,B)) = k2_xboole_0(k3_tarski(A),k3_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_zfmisc_1)).

tff(f_29,axiom,(
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

tff(f_33,axiom,(
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

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(A_42,k2_xboole_0(B_43,C_44))
      | ~ r1_tarski(k4_xboole_0(A_42,B_43),C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_74,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(B_2,A_1)) ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_10,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_tarski(A_11),k3_tarski(B_12)) = k3_tarski(k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_75,plain,(
    ! [A_45,B_46] : r1_tarski(A_45,k2_xboole_0(B_46,A_45)) ),
    inference(resolution,[status(thm)],[c_2,c_66])).

tff(c_82,plain,(
    ! [B_12,A_11] : r1_tarski(k3_tarski(B_12),k3_tarski(k2_xboole_0(A_11,B_12))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_269,plain,(
    ! [C_79,A_80,B_81] :
      ( m1_subset_1(C_79,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80))))
      | ~ r1_tarski(C_79,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80))))
      | ~ l1_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_722,plain,(
    ! [A_154,B_155,A_156,C_157] :
      ( m1_subset_1(k4_xboole_0(A_154,B_155),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156))))
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156))))
      | ~ l1_struct_0(A_156)
      | ~ r1_tarski(A_154,k2_xboole_0(B_155,C_157)) ) ),
    inference(resolution,[status(thm)],[c_6,c_269])).

tff(c_731,plain,(
    ! [A_154,B_155] :
      ( m1_subset_1(k4_xboole_0(A_154,B_155),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ l1_struct_0('#skF_1')
      | ~ r1_tarski(A_154,k2_xboole_0(B_155,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_24,c_722])).

tff(c_756,plain,(
    ! [A_160,B_161] :
      ( m1_subset_1(k4_xboole_0(A_160,B_161),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
      | ~ r1_tarski(A_160,k2_xboole_0(B_161,'#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_731])).

tff(c_16,plain,(
    ! [A_18,B_19] :
      ( k5_setfam_1(A_18,B_19) = k3_tarski(B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_893,plain,(
    ! [A_181,B_182] :
      ( k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0(A_181,B_182)) = k3_tarski(k4_xboole_0(A_181,B_182))
      | ~ r1_tarski(A_181,k2_xboole_0(B_182,'#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_756,c_16])).

tff(c_47,plain,(
    ! [A_40,B_41] :
      ( k5_setfam_1(A_40,B_41) = k3_tarski(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(k1_zfmisc_1(A_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_55,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_47])).

tff(c_105,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k5_setfam_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_105])).

tff(c_118,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_112])).

tff(c_177,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_189,plain,(
    ! [C_68] : k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),C_68) = k4_xboole_0(k3_tarski('#skF_2'),C_68) ),
    inference(resolution,[status(thm)],[c_118,c_177])).

tff(c_192,plain,(
    ! [C_68] : k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2',C_68) = k4_xboole_0('#skF_2',C_68) ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_54,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3') = k3_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_20,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_20])).

tff(c_61,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')),'#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_60])).

tff(c_202,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_61])).

tff(c_250,plain,(
    ~ r1_tarski(k4_xboole_0(k3_tarski('#skF_2'),k3_tarski('#skF_3')),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_202])).

tff(c_348,plain,(
    ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k5_setfam_1(u1_struct_0('#skF_1'),k4_xboole_0('#skF_2','#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6,c_250])).

tff(c_902,plain,
    ( ~ r1_tarski(k3_tarski('#skF_2'),k2_xboole_0(k3_tarski('#skF_3'),k3_tarski(k4_xboole_0('#skF_2','#skF_3'))))
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_348])).

tff(c_919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_82,c_4,c_10,c_902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  
% 3.52/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.56  %$ r1_tarski > m1_subset_1 > l1_struct_0 > k7_subset_1 > k5_setfam_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.52/1.56  
% 3.52/1.56  %Foreground sorts:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Background operators:
% 3.52/1.56  
% 3.52/1.56  
% 3.52/1.56  %Foreground operators:
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.52/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.56  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.52/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.52/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.52/1.56  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.52/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.52/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.56  
% 3.68/1.58  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.68/1.58  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.68/1.58  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_xboole_0(A, B)) = k2_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_zfmisc_1)).
% 3.68/1.58  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.68/1.58  tff(f_72, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => r1_tarski(k7_subset_1(u1_struct_0(A), k5_setfam_1(u1_struct_0(A), B), k5_setfam_1(u1_struct_0(A), C)), k5_setfam_1(u1_struct_0(A), k7_subset_1(k1_zfmisc_1(u1_struct_0(A)), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tops_2)).
% 3.68/1.58  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.68/1.58  tff(f_61, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_tops_2)).
% 3.68/1.58  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 3.68/1.58  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.68/1.58  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.68/1.58  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.68/1.58  tff(c_66, plain, (![A_42, B_43, C_44]: (r1_tarski(A_42, k2_xboole_0(B_43, C_44)) | ~r1_tarski(k4_xboole_0(A_42, B_43), C_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.68/1.58  tff(c_74, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(B_2, A_1)))), inference(resolution, [status(thm)], [c_2, c_66])).
% 3.68/1.58  tff(c_10, plain, (![A_11, B_12]: (k2_xboole_0(k3_tarski(A_11), k3_tarski(B_12))=k3_tarski(k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.68/1.58  tff(c_75, plain, (![A_45, B_46]: (r1_tarski(A_45, k2_xboole_0(B_46, A_45)))), inference(resolution, [status(thm)], [c_2, c_66])).
% 3.68/1.58  tff(c_82, plain, (![B_12, A_11]: (r1_tarski(k3_tarski(B_12), k3_tarski(k2_xboole_0(A_11, B_12))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_75])).
% 3.68/1.58  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.68/1.58  tff(c_26, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.68/1.58  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.68/1.58  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.68/1.58  tff(c_269, plain, (![C_79, A_80, B_81]: (m1_subset_1(C_79, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80)))) | ~r1_tarski(C_79, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_80)))) | ~l1_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.68/1.58  tff(c_722, plain, (![A_154, B_155, A_156, C_157]: (m1_subset_1(k4_xboole_0(A_154, B_155), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156)))) | ~m1_subset_1(C_157, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_156)))) | ~l1_struct_0(A_156) | ~r1_tarski(A_154, k2_xboole_0(B_155, C_157)))), inference(resolution, [status(thm)], [c_6, c_269])).
% 3.68/1.58  tff(c_731, plain, (![A_154, B_155]: (m1_subset_1(k4_xboole_0(A_154, B_155), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~l1_struct_0('#skF_1') | ~r1_tarski(A_154, k2_xboole_0(B_155, '#skF_2')))), inference(resolution, [status(thm)], [c_24, c_722])).
% 3.68/1.58  tff(c_756, plain, (![A_160, B_161]: (m1_subset_1(k4_xboole_0(A_160, B_161), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) | ~r1_tarski(A_160, k2_xboole_0(B_161, '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_731])).
% 3.68/1.58  tff(c_16, plain, (![A_18, B_19]: (k5_setfam_1(A_18, B_19)=k3_tarski(B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.68/1.58  tff(c_893, plain, (![A_181, B_182]: (k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0(A_181, B_182))=k3_tarski(k4_xboole_0(A_181, B_182)) | ~r1_tarski(A_181, k2_xboole_0(B_182, '#skF_2')))), inference(resolution, [status(thm)], [c_756, c_16])).
% 3.68/1.58  tff(c_47, plain, (![A_40, B_41]: (k5_setfam_1(A_40, B_41)=k3_tarski(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(k1_zfmisc_1(A_40))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.68/1.58  tff(c_55, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_24, c_47])).
% 3.68/1.58  tff(c_105, plain, (![A_51, B_52]: (m1_subset_1(k5_setfam_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.68/1.58  tff(c_112, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_55, c_105])).
% 3.68/1.58  tff(c_118, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_112])).
% 3.68/1.58  tff(c_177, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.68/1.58  tff(c_189, plain, (![C_68]: (k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), C_68)=k4_xboole_0(k3_tarski('#skF_2'), C_68))), inference(resolution, [status(thm)], [c_118, c_177])).
% 3.68/1.58  tff(c_192, plain, (![C_68]: (k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', C_68)=k4_xboole_0('#skF_2', C_68))), inference(resolution, [status(thm)], [c_24, c_177])).
% 3.68/1.58  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.68/1.58  tff(c_54, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')=k3_tarski('#skF_3')), inference(resolution, [status(thm)], [c_22, c_47])).
% 3.68/1.58  tff(c_20, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.68/1.58  tff(c_60, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_20])).
% 3.68/1.58  tff(c_61, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k7_subset_1(k1_zfmisc_1(u1_struct_0('#skF_1')), '#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_60])).
% 3.68/1.58  tff(c_202, plain, (~r1_tarski(k7_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_61])).
% 3.68/1.58  tff(c_250, plain, (~r1_tarski(k4_xboole_0(k3_tarski('#skF_2'), k3_tarski('#skF_3')), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_202])).
% 3.68/1.58  tff(c_348, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k5_setfam_1(u1_struct_0('#skF_1'), k4_xboole_0('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_6, c_250])).
% 3.68/1.58  tff(c_902, plain, (~r1_tarski(k3_tarski('#skF_2'), k2_xboole_0(k3_tarski('#skF_3'), k3_tarski(k4_xboole_0('#skF_2', '#skF_3')))) | ~r1_tarski('#skF_2', k2_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_893, c_348])).
% 3.68/1.58  tff(c_919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_82, c_4, c_10, c_902])).
% 3.68/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.68/1.58  
% 3.68/1.58  Inference rules
% 3.68/1.58  ----------------------
% 3.68/1.58  #Ref     : 0
% 3.68/1.58  #Sup     : 233
% 3.68/1.58  #Fact    : 0
% 3.68/1.58  #Define  : 0
% 3.68/1.58  #Split   : 0
% 3.68/1.58  #Chain   : 0
% 3.68/1.58  #Close   : 0
% 3.68/1.58  
% 3.68/1.58  Ordering : KBO
% 3.68/1.58  
% 3.68/1.58  Simplification rules
% 3.68/1.58  ----------------------
% 3.68/1.58  #Subsume      : 0
% 3.68/1.58  #Demod        : 85
% 3.68/1.58  #Tautology    : 40
% 3.68/1.58  #SimpNegUnit  : 0
% 3.68/1.58  #BackRed      : 3
% 3.68/1.58  
% 3.68/1.58  #Partial instantiations: 0
% 3.68/1.58  #Strategies tried      : 1
% 3.68/1.58  
% 3.68/1.58  Timing (in seconds)
% 3.68/1.58  ----------------------
% 3.68/1.58  Preprocessing        : 0.30
% 3.68/1.58  Parsing              : 0.17
% 3.68/1.58  CNF conversion       : 0.02
% 3.68/1.58  Main loop            : 0.50
% 3.68/1.58  Inferencing          : 0.17
% 3.68/1.58  Reduction            : 0.17
% 3.68/1.58  Demodulation         : 0.13
% 3.68/1.58  BG Simplification    : 0.02
% 3.68/1.58  Subsumption          : 0.10
% 3.68/1.58  Abstraction          : 0.02
% 3.68/1.58  MUC search           : 0.00
% 3.68/1.58  Cooper               : 0.00
% 3.68/1.58  Total                : 0.83
% 3.68/1.58  Index Insertion      : 0.00
% 3.68/1.58  Index Deletion       : 0.00
% 3.68/1.58  Index Matching       : 0.00
% 3.68/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

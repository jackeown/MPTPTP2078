%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:02 EST 2020

% Result     : Theorem 4.64s
% Output     : CNFRefutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 270 expanded)
%              Number of leaves         :   29 ( 106 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 659 expanded)
%              Number of equality atoms :   21 ( 123 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v4_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v4_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v4_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v4_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_30,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_42,plain,(
    ~ v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_98,plain,(
    ! [B_60,A_61] :
      ( l1_pre_topc(B_60)
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_98])).

tff(c_104,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101])).

tff(c_16,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_85,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_108,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_104,c_85])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_41,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_109,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_41])).

tff(c_114,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(A_62,B_63)
      | ~ m1_subset_1(A_62,k1_zfmisc_1(B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_109,c_114])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_124,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_86,plain,(
    ! [A_55] :
      ( u1_struct_0(A_55) = k2_struct_0(A_55)
      | ~ l1_pre_topc(A_55) ) ),
    inference(resolution,[status(thm)],[c_16,c_81])).

tff(c_90,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_86])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_91,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_38])).

tff(c_34,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_143,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_150,plain,(
    ! [B_65] : k9_subset_1(k2_struct_0('#skF_4'),B_65,'#skF_3') = k3_xboole_0(B_65,'#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_143])).

tff(c_153,plain,(
    ! [A_67,C_68,B_69] :
      ( k9_subset_1(A_67,C_68,B_69) = k9_subset_1(A_67,B_69,C_68)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [B_69] : k9_subset_1(k2_struct_0('#skF_4'),B_69,'#skF_3') = k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_69) ),
    inference(resolution,[status(thm)],[c_109,c_153])).

tff(c_208,plain,(
    ! [B_69] : k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_69) = k3_xboole_0(B_69,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_160])).

tff(c_455,plain,(
    ! [B_117,D_118,A_119] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_117),D_118,k2_struct_0(B_117)),B_117)
      | ~ v4_pre_topc(D_118,A_119)
      | ~ m1_subset_1(D_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_117),D_118,k2_struct_0(B_117)),k1_zfmisc_1(u1_struct_0(B_117)))
      | ~ m1_pre_topc(B_117,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_464,plain,(
    ! [B_117,D_118] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_117),D_118,k2_struct_0(B_117)),B_117)
      | ~ v4_pre_topc(D_118,'#skF_2')
      | ~ m1_subset_1(D_118,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_117),D_118,k2_struct_0(B_117)),k1_zfmisc_1(u1_struct_0(B_117)))
      | ~ m1_pre_topc(B_117,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_455])).

tff(c_2316,plain,(
    ! [B_243,D_244] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_243),D_244,k2_struct_0(B_243)),B_243)
      | ~ v4_pre_topc(D_244,'#skF_2')
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_243),D_244,k2_struct_0(B_243)),k1_zfmisc_1(u1_struct_0(B_243)))
      | ~ m1_pre_topc(B_243,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_464])).

tff(c_2334,plain,(
    ! [D_244] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),D_244,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(D_244,'#skF_2')
      | ~ m1_subset_1(D_244,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'),D_244,k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_2316])).

tff(c_2355,plain,(
    ! [D_245] :
      ( v4_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),D_245,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(D_245,'#skF_2')
      | ~ m1_subset_1(D_245,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'),D_245,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_108,c_108,c_2334])).

tff(c_2366,plain,
    ( v4_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',k2_struct_0('#skF_4')),'#skF_4')
    | ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1(k3_xboole_0(k2_struct_0('#skF_4'),'#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_2355])).

tff(c_2371,plain,(
    v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_130,c_2,c_91,c_34,c_130,c_2,c_208,c_2366])).

tff(c_2373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.64/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.86  
% 4.64/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.86  %$ v4_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.64/1.86  
% 4.64/1.86  %Foreground sorts:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Background operators:
% 4.64/1.86  
% 4.64/1.86  
% 4.64/1.86  %Foreground operators:
% 4.64/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.64/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.64/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.64/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.64/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.64/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.64/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.64/1.86  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.64/1.86  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.64/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.64/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.64/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.64/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.64/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.64/1.86  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.64/1.87  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.64/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.64/1.87  
% 4.64/1.88  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_tops_2)).
% 4.64/1.88  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.64/1.88  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.64/1.88  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.64/1.88  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.64/1.88  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.64/1.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.64/1.88  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.64/1.88  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 4.64/1.88  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_pre_topc)).
% 4.64/1.88  tff(c_30, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.88  tff(c_28, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.88  tff(c_42, plain, (~v4_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28])).
% 4.64/1.88  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.88  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.88  tff(c_98, plain, (![B_60, A_61]: (l1_pre_topc(B_60) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.64/1.88  tff(c_101, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_36, c_98])).
% 4.64/1.88  tff(c_104, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_101])).
% 4.64/1.88  tff(c_16, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.64/1.88  tff(c_81, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.64/1.88  tff(c_85, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_16, c_81])).
% 4.64/1.88  tff(c_108, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_104, c_85])).
% 4.64/1.88  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.88  tff(c_41, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 4.64/1.88  tff(c_109, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_41])).
% 4.64/1.88  tff(c_114, plain, (![A_62, B_63]: (r1_tarski(A_62, B_63) | ~m1_subset_1(A_62, k1_zfmisc_1(B_63)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.64/1.88  tff(c_124, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_109, c_114])).
% 4.64/1.88  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.64/1.88  tff(c_130, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_124, c_4])).
% 4.64/1.88  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.64/1.88  tff(c_86, plain, (![A_55]: (u1_struct_0(A_55)=k2_struct_0(A_55) | ~l1_pre_topc(A_55))), inference(resolution, [status(thm)], [c_16, c_81])).
% 4.64/1.88  tff(c_90, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_86])).
% 4.64/1.88  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.88  tff(c_91, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_38])).
% 4.64/1.88  tff(c_34, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.64/1.88  tff(c_143, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.64/1.88  tff(c_150, plain, (![B_65]: (k9_subset_1(k2_struct_0('#skF_4'), B_65, '#skF_3')=k3_xboole_0(B_65, '#skF_3'))), inference(resolution, [status(thm)], [c_109, c_143])).
% 4.64/1.88  tff(c_153, plain, (![A_67, C_68, B_69]: (k9_subset_1(A_67, C_68, B_69)=k9_subset_1(A_67, B_69, C_68) | ~m1_subset_1(C_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.64/1.88  tff(c_160, plain, (![B_69]: (k9_subset_1(k2_struct_0('#skF_4'), B_69, '#skF_3')=k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_69))), inference(resolution, [status(thm)], [c_109, c_153])).
% 4.64/1.88  tff(c_208, plain, (![B_69]: (k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_69)=k3_xboole_0(B_69, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_150, c_160])).
% 4.64/1.88  tff(c_455, plain, (![B_117, D_118, A_119]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_117), D_118, k2_struct_0(B_117)), B_117) | ~v4_pre_topc(D_118, A_119) | ~m1_subset_1(D_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_117), D_118, k2_struct_0(B_117)), k1_zfmisc_1(u1_struct_0(B_117))) | ~m1_pre_topc(B_117, A_119) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.64/1.88  tff(c_464, plain, (![B_117, D_118]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_117), D_118, k2_struct_0(B_117)), B_117) | ~v4_pre_topc(D_118, '#skF_2') | ~m1_subset_1(D_118, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_117), D_118, k2_struct_0(B_117)), k1_zfmisc_1(u1_struct_0(B_117))) | ~m1_pre_topc(B_117, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_455])).
% 4.64/1.88  tff(c_2316, plain, (![B_243, D_244]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_243), D_244, k2_struct_0(B_243)), B_243) | ~v4_pre_topc(D_244, '#skF_2') | ~m1_subset_1(D_244, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_243), D_244, k2_struct_0(B_243)), k1_zfmisc_1(u1_struct_0(B_243))) | ~m1_pre_topc(B_243, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_464])).
% 4.64/1.88  tff(c_2334, plain, (![D_244]: (v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), D_244, k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc(D_244, '#skF_2') | ~m1_subset_1(D_244, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'), D_244, k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_108, c_2316])).
% 4.64/1.88  tff(c_2355, plain, (![D_245]: (v4_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), D_245, k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc(D_245, '#skF_2') | ~m1_subset_1(D_245, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'), D_245, k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_108, c_108, c_2334])).
% 4.64/1.88  tff(c_2366, plain, (v4_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k3_xboole_0(k2_struct_0('#skF_4'), '#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_208, c_2355])).
% 4.64/1.88  tff(c_2371, plain, (v4_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_130, c_2, c_91, c_34, c_130, c_2, c_208, c_2366])).
% 4.64/1.88  tff(c_2373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2371])).
% 4.64/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.64/1.88  
% 4.64/1.88  Inference rules
% 4.64/1.88  ----------------------
% 4.64/1.88  #Ref     : 0
% 4.64/1.88  #Sup     : 539
% 4.64/1.88  #Fact    : 0
% 4.64/1.88  #Define  : 0
% 4.64/1.88  #Split   : 3
% 4.64/1.88  #Chain   : 0
% 4.64/1.88  #Close   : 0
% 4.64/1.88  
% 4.64/1.88  Ordering : KBO
% 4.64/1.88  
% 4.64/1.88  Simplification rules
% 4.64/1.88  ----------------------
% 4.64/1.88  #Subsume      : 166
% 4.64/1.88  #Demod        : 315
% 4.64/1.88  #Tautology    : 199
% 4.64/1.88  #SimpNegUnit  : 1
% 4.64/1.88  #BackRed      : 2
% 4.64/1.88  
% 4.64/1.88  #Partial instantiations: 0
% 4.64/1.88  #Strategies tried      : 1
% 4.64/1.88  
% 4.64/1.88  Timing (in seconds)
% 4.64/1.88  ----------------------
% 4.64/1.88  Preprocessing        : 0.32
% 4.64/1.88  Parsing              : 0.17
% 4.64/1.88  CNF conversion       : 0.02
% 4.64/1.88  Main loop            : 0.80
% 4.64/1.88  Inferencing          : 0.31
% 4.64/1.88  Reduction            : 0.27
% 4.64/1.88  Demodulation         : 0.20
% 4.64/1.88  BG Simplification    : 0.04
% 4.64/1.88  Subsumption          : 0.14
% 4.64/1.88  Abstraction          : 0.05
% 4.64/1.88  MUC search           : 0.00
% 4.64/1.88  Cooper               : 0.00
% 4.64/1.88  Total                : 1.15
% 4.64/1.88  Index Insertion      : 0.00
% 4.64/1.88  Index Deletion       : 0.00
% 4.64/1.88  Index Matching       : 0.00
% 4.64/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------

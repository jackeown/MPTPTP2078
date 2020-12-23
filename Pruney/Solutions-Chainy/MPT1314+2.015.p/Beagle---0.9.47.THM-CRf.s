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
% DateTime   : Thu Dec  3 10:23:01 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 191 expanded)
%              Number of leaves         :   32 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  100 ( 437 expanded)
%              Number of equality atoms :   17 (  79 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_pre_topc(C,A)
               => ( v3_pre_topc(B,A)
                 => ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                     => ( D = B
                       => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => ( v3_pre_topc(C,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & k9_subset_1(u1_struct_0(B),D,k2_struct_0(B)) = C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_2)).

tff(c_32,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    ~ v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_85,plain,(
    ! [B_57,A_58] :
      ( l1_pre_topc(B_57)
      | ~ m1_pre_topc(B_57,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_85])).

tff(c_91,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_88])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_61,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = k2_struct_0(A_53)
      | ~ l1_struct_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_13] :
      ( u1_struct_0(A_13) = k2_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(resolution,[status(thm)],[c_18,c_61])).

tff(c_95,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_65])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_96,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_43])).

tff(c_66,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_18,c_61])).

tff(c_70,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_66])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_71,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_40])).

tff(c_36,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_102,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(A_61,B_62)
      | ~ m1_subset_1(A_61,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_96,c_102])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_112,c_2])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_150,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_162,plain,(
    ! [A_4,B_68] : k9_subset_1(A_4,B_68,A_4) = k3_xboole_0(B_68,A_4) ),
    inference(resolution,[status(thm)],[c_45,c_150])).

tff(c_377,plain,(
    ! [B_114,D_115,A_116] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_114),D_115,k2_struct_0(B_114)),B_114)
      | ~ v3_pre_topc(D_115,A_116)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_114),D_115,k2_struct_0(B_114)),k1_zfmisc_1(u1_struct_0(B_114)))
      | ~ m1_pre_topc(B_114,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_386,plain,(
    ! [B_114,D_115] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_114),D_115,k2_struct_0(B_114)),B_114)
      | ~ v3_pre_topc(D_115,'#skF_2')
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_114),D_115,k2_struct_0(B_114)),k1_zfmisc_1(u1_struct_0(B_114)))
      | ~ m1_pre_topc(B_114,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_377])).

tff(c_443,plain,(
    ! [B_123,D_124] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_123),D_124,k2_struct_0(B_123)),B_123)
      | ~ v3_pre_topc(D_124,'#skF_2')
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_123),D_124,k2_struct_0(B_123)),k1_zfmisc_1(u1_struct_0(B_123)))
      | ~ m1_pre_topc(B_123,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_386])).

tff(c_452,plain,(
    ! [D_124] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),D_124,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(D_124,'#skF_2')
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'),D_124,k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_443])).

tff(c_469,plain,(
    ! [D_125] :
      ( v3_pre_topc(k3_xboole_0(D_125,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(D_125,'#skF_2')
      | ~ m1_subset_1(D_125,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_xboole_0(D_125,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_162,c_95,c_162,c_95,c_452])).

tff(c_475,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_3',k2_struct_0('#skF_4')),'#skF_4')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_469])).

tff(c_484,plain,(
    v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_71,c_36,c_132,c_475])).

tff(c_486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_484])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:58:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.44  
% 2.89/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.44  %$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.89/1.44  
% 2.89/1.44  %Foreground sorts:
% 2.89/1.44  
% 2.89/1.44  
% 2.89/1.44  %Background operators:
% 2.89/1.44  
% 2.89/1.44  
% 2.89/1.44  %Foreground operators:
% 2.89/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.89/1.44  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.89/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.89/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.89/1.44  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.89/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.89/1.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.89/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.89/1.44  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.89/1.44  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.89/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.89/1.44  
% 2.89/1.46  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 2.89/1.46  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.89/1.46  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.89/1.46  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.89/1.46  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.89/1.46  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.89/1.46  tff(f_31, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.89/1.46  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.89/1.46  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.89/1.46  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 2.89/1.46  tff(c_32, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.46  tff(c_30, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.46  tff(c_44, plain, (~v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 2.89/1.46  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.46  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.46  tff(c_85, plain, (![B_57, A_58]: (l1_pre_topc(B_57) | ~m1_pre_topc(B_57, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.89/1.46  tff(c_88, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_85])).
% 2.89/1.46  tff(c_91, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_88])).
% 2.89/1.46  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.46  tff(c_61, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.46  tff(c_65, plain, (![A_13]: (u1_struct_0(A_13)=k2_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_18, c_61])).
% 2.89/1.46  tff(c_95, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_91, c_65])).
% 2.89/1.46  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.46  tff(c_43, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 2.89/1.46  tff(c_96, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_43])).
% 2.89/1.46  tff(c_66, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_18, c_61])).
% 2.89/1.46  tff(c_70, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_66])).
% 2.89/1.46  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.46  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40])).
% 2.89/1.46  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.89/1.46  tff(c_102, plain, (![A_61, B_62]: (r1_tarski(A_61, B_62) | ~m1_subset_1(A_61, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.46  tff(c_112, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_96, c_102])).
% 2.89/1.46  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.89/1.46  tff(c_132, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_112, c_2])).
% 2.89/1.46  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.89/1.46  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.46  tff(c_45, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.89/1.46  tff(c_150, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.89/1.46  tff(c_162, plain, (![A_4, B_68]: (k9_subset_1(A_4, B_68, A_4)=k3_xboole_0(B_68, A_4))), inference(resolution, [status(thm)], [c_45, c_150])).
% 2.89/1.46  tff(c_377, plain, (![B_114, D_115, A_116]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_114), D_115, k2_struct_0(B_114)), B_114) | ~v3_pre_topc(D_115, A_116) | ~m1_subset_1(D_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_114), D_115, k2_struct_0(B_114)), k1_zfmisc_1(u1_struct_0(B_114))) | ~m1_pre_topc(B_114, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.89/1.46  tff(c_386, plain, (![B_114, D_115]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_114), D_115, k2_struct_0(B_114)), B_114) | ~v3_pre_topc(D_115, '#skF_2') | ~m1_subset_1(D_115, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_114), D_115, k2_struct_0(B_114)), k1_zfmisc_1(u1_struct_0(B_114))) | ~m1_pre_topc(B_114, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_377])).
% 2.89/1.46  tff(c_443, plain, (![B_123, D_124]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_123), D_124, k2_struct_0(B_123)), B_123) | ~v3_pre_topc(D_124, '#skF_2') | ~m1_subset_1(D_124, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_123), D_124, k2_struct_0(B_123)), k1_zfmisc_1(u1_struct_0(B_123))) | ~m1_pre_topc(B_123, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_386])).
% 2.89/1.46  tff(c_452, plain, (![D_124]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), D_124, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(D_124, '#skF_2') | ~m1_subset_1(D_124, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'), D_124, k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_443])).
% 2.89/1.46  tff(c_469, plain, (![D_125]: (v3_pre_topc(k3_xboole_0(D_125, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(D_125, '#skF_2') | ~m1_subset_1(D_125, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k3_xboole_0(D_125, k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_162, c_95, c_162, c_95, c_452])).
% 2.89/1.46  tff(c_475, plain, (v3_pre_topc(k3_xboole_0('#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_132, c_469])).
% 2.89/1.46  tff(c_484, plain, (v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_71, c_36, c_132, c_475])).
% 2.89/1.46  tff(c_486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_484])).
% 2.89/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.46  
% 2.89/1.46  Inference rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Ref     : 0
% 2.89/1.46  #Sup     : 106
% 2.89/1.46  #Fact    : 0
% 2.89/1.46  #Define  : 0
% 2.89/1.46  #Split   : 2
% 2.89/1.46  #Chain   : 0
% 2.89/1.46  #Close   : 0
% 2.89/1.46  
% 2.89/1.46  Ordering : KBO
% 2.89/1.46  
% 2.89/1.46  Simplification rules
% 2.89/1.46  ----------------------
% 2.89/1.46  #Subsume      : 8
% 2.89/1.46  #Demod        : 49
% 2.89/1.46  #Tautology    : 36
% 2.89/1.46  #SimpNegUnit  : 1
% 2.89/1.46  #BackRed      : 2
% 2.89/1.46  
% 2.89/1.46  #Partial instantiations: 0
% 2.89/1.46  #Strategies tried      : 1
% 2.89/1.46  
% 2.89/1.46  Timing (in seconds)
% 2.89/1.46  ----------------------
% 2.89/1.46  Preprocessing        : 0.33
% 2.89/1.46  Parsing              : 0.17
% 2.89/1.46  CNF conversion       : 0.02
% 2.89/1.46  Main loop            : 0.36
% 2.89/1.46  Inferencing          : 0.13
% 2.89/1.46  Reduction            : 0.11
% 2.89/1.46  Demodulation         : 0.08
% 2.89/1.46  BG Simplification    : 0.02
% 2.89/1.46  Subsumption          : 0.07
% 2.89/1.46  Abstraction          : 0.02
% 2.89/1.46  MUC search           : 0.00
% 2.89/1.46  Cooper               : 0.00
% 2.89/1.46  Total                : 0.72
% 2.89/1.46  Index Insertion      : 0.00
% 2.89/1.46  Index Deletion       : 0.00
% 2.89/1.46  Index Matching       : 0.00
% 2.89/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

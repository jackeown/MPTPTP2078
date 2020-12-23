%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:01 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 190 expanded)
%              Number of leaves         :   31 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  101 ( 437 expanded)
%              Number of equality atoms :   17 (  79 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
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

tff(c_76,plain,(
    ! [B_55,A_56] :
      ( l1_pre_topc(B_55)
      | ~ m1_pre_topc(B_55,A_56)
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_82,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_79])).

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

tff(c_99,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_65])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_102,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_43])).

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

tff(c_83,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_43,c_83])).

tff(c_101,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_94])).

tff(c_112,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_101,c_112])).

tff(c_6,plain,(
    ! [A_5] : k2_subset_1(A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_162,plain,(
    ! [A_67,B_68,C_69] :
      ( k9_subset_1(A_67,B_68,C_69) = k3_xboole_0(B_68,C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_174,plain,(
    ! [A_6,B_68] : k9_subset_1(A_6,B_68,A_6) = k3_xboole_0(B_68,A_6) ),
    inference(resolution,[status(thm)],[c_45,c_162])).

tff(c_601,plain,(
    ! [B_115,D_116,A_117] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_115),D_116,k2_struct_0(B_115)),B_115)
      | ~ v3_pre_topc(D_116,A_117)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_115),D_116,k2_struct_0(B_115)),k1_zfmisc_1(u1_struct_0(B_115)))
      | ~ m1_pre_topc(B_115,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_610,plain,(
    ! [B_115,D_116] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_115),D_116,k2_struct_0(B_115)),B_115)
      | ~ v3_pre_topc(D_116,'#skF_2')
      | ~ m1_subset_1(D_116,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_115),D_116,k2_struct_0(B_115)),k1_zfmisc_1(u1_struct_0(B_115)))
      | ~ m1_pre_topc(B_115,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_601])).

tff(c_1822,plain,(
    ! [B_197,D_198] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_197),D_198,k2_struct_0(B_197)),B_197)
      | ~ v3_pre_topc(D_198,'#skF_2')
      | ~ m1_subset_1(D_198,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_197),D_198,k2_struct_0(B_197)),k1_zfmisc_1(u1_struct_0(B_197)))
      | ~ m1_pre_topc(B_197,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_610])).

tff(c_1831,plain,(
    ! [D_198] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),D_198,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(D_198,'#skF_2')
      | ~ m1_subset_1(D_198,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'),D_198,k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_1822])).

tff(c_1848,plain,(
    ! [D_199] :
      ( v3_pre_topc(k3_xboole_0(D_199,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(D_199,'#skF_2')
      | ~ m1_subset_1(D_199,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ m1_subset_1(k3_xboole_0(D_199,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_174,c_99,c_174,c_99,c_1831])).

tff(c_1860,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_3',k2_struct_0('#skF_4')),'#skF_4')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_1848])).

tff(c_1869,plain,(
    v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_71,c_36,c_122,c_1860])).

tff(c_1871,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1869])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:40 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.73  
% 4.09/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.73  %$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 4.09/1.73  
% 4.09/1.73  %Foreground sorts:
% 4.09/1.73  
% 4.09/1.73  
% 4.09/1.73  %Background operators:
% 4.09/1.73  
% 4.09/1.73  
% 4.09/1.73  %Foreground operators:
% 4.09/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.09/1.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.09/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.09/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.09/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.09/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.09/1.73  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.09/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.09/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.09/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.09/1.73  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.09/1.73  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.09/1.73  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.09/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.09/1.73  
% 4.09/1.75  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 4.09/1.75  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.09/1.75  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.09/1.75  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.09/1.75  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.09/1.75  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.09/1.75  tff(f_33, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.09/1.75  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.09/1.75  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.09/1.75  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 4.09/1.75  tff(c_32, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.09/1.75  tff(c_30, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.09/1.75  tff(c_44, plain, (~v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 4.09/1.75  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.09/1.75  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.09/1.75  tff(c_76, plain, (![B_55, A_56]: (l1_pre_topc(B_55) | ~m1_pre_topc(B_55, A_56) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.09/1.75  tff(c_79, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_76])).
% 4.09/1.75  tff(c_82, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_79])).
% 4.09/1.75  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.75  tff(c_61, plain, (![A_53]: (u1_struct_0(A_53)=k2_struct_0(A_53) | ~l1_struct_0(A_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.09/1.75  tff(c_65, plain, (![A_13]: (u1_struct_0(A_13)=k2_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(resolution, [status(thm)], [c_18, c_61])).
% 4.09/1.75  tff(c_99, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_82, c_65])).
% 4.09/1.75  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.09/1.75  tff(c_43, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 4.09/1.75  tff(c_102, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_43])).
% 4.09/1.75  tff(c_66, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_18, c_61])).
% 4.09/1.75  tff(c_70, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_66])).
% 4.09/1.75  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.09/1.75  tff(c_71, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_40])).
% 4.09/1.75  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.09/1.75  tff(c_83, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.75  tff(c_94, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_43, c_83])).
% 4.09/1.75  tff(c_101, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_94])).
% 4.09/1.75  tff(c_112, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.75  tff(c_122, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_101, c_112])).
% 4.09/1.75  tff(c_6, plain, (![A_5]: (k2_subset_1(A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.09/1.75  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.75  tff(c_45, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 4.09/1.75  tff(c_162, plain, (![A_67, B_68, C_69]: (k9_subset_1(A_67, B_68, C_69)=k3_xboole_0(B_68, C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.09/1.75  tff(c_174, plain, (![A_6, B_68]: (k9_subset_1(A_6, B_68, A_6)=k3_xboole_0(B_68, A_6))), inference(resolution, [status(thm)], [c_45, c_162])).
% 4.09/1.75  tff(c_601, plain, (![B_115, D_116, A_117]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_115), D_116, k2_struct_0(B_115)), B_115) | ~v3_pre_topc(D_116, A_117) | ~m1_subset_1(D_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_115), D_116, k2_struct_0(B_115)), k1_zfmisc_1(u1_struct_0(B_115))) | ~m1_pre_topc(B_115, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.09/1.75  tff(c_610, plain, (![B_115, D_116]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_115), D_116, k2_struct_0(B_115)), B_115) | ~v3_pre_topc(D_116, '#skF_2') | ~m1_subset_1(D_116, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_115), D_116, k2_struct_0(B_115)), k1_zfmisc_1(u1_struct_0(B_115))) | ~m1_pre_topc(B_115, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_601])).
% 4.09/1.75  tff(c_1822, plain, (![B_197, D_198]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_197), D_198, k2_struct_0(B_197)), B_197) | ~v3_pre_topc(D_198, '#skF_2') | ~m1_subset_1(D_198, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_197), D_198, k2_struct_0(B_197)), k1_zfmisc_1(u1_struct_0(B_197))) | ~m1_pre_topc(B_197, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_610])).
% 4.09/1.75  tff(c_1831, plain, (![D_198]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), D_198, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(D_198, '#skF_2') | ~m1_subset_1(D_198, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'), D_198, k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_99, c_1822])).
% 4.09/1.75  tff(c_1848, plain, (![D_199]: (v3_pre_topc(k3_xboole_0(D_199, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(D_199, '#skF_2') | ~m1_subset_1(D_199, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1(k3_xboole_0(D_199, k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_174, c_99, c_174, c_99, c_1831])).
% 4.09/1.75  tff(c_1860, plain, (v3_pre_topc(k3_xboole_0('#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc('#skF_3', '#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_122, c_1848])).
% 4.09/1.75  tff(c_1869, plain, (v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_71, c_36, c_122, c_1860])).
% 4.09/1.75  tff(c_1871, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1869])).
% 4.09/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.75  
% 4.09/1.75  Inference rules
% 4.09/1.75  ----------------------
% 4.09/1.75  #Ref     : 0
% 4.09/1.75  #Sup     : 433
% 4.09/1.75  #Fact    : 0
% 4.09/1.75  #Define  : 0
% 4.09/1.75  #Split   : 5
% 4.09/1.75  #Chain   : 0
% 4.09/1.75  #Close   : 0
% 4.09/1.75  
% 4.09/1.75  Ordering : KBO
% 4.09/1.75  
% 4.09/1.75  Simplification rules
% 4.09/1.75  ----------------------
% 4.09/1.75  #Subsume      : 59
% 4.09/1.75  #Demod        : 625
% 4.09/1.75  #Tautology    : 171
% 4.09/1.75  #SimpNegUnit  : 2
% 4.09/1.75  #BackRed      : 3
% 4.09/1.75  
% 4.09/1.75  #Partial instantiations: 0
% 4.09/1.75  #Strategies tried      : 1
% 4.09/1.75  
% 4.09/1.75  Timing (in seconds)
% 4.09/1.75  ----------------------
% 4.09/1.75  Preprocessing        : 0.31
% 4.09/1.75  Parsing              : 0.16
% 4.09/1.75  CNF conversion       : 0.02
% 4.09/1.75  Main loop            : 0.67
% 4.09/1.75  Inferencing          : 0.22
% 4.09/1.75  Reduction            : 0.26
% 4.09/1.75  Demodulation         : 0.20
% 4.09/1.75  BG Simplification    : 0.03
% 4.09/1.75  Subsumption          : 0.12
% 4.09/1.75  Abstraction          : 0.04
% 4.09/1.75  MUC search           : 0.00
% 4.09/1.75  Cooper               : 0.00
% 4.09/1.75  Total                : 1.01
% 4.09/1.75  Index Insertion      : 0.00
% 4.09/1.75  Index Deletion       : 0.00
% 4.09/1.75  Index Matching       : 0.00
% 4.09/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:03 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 194 expanded)
%              Number of leaves         :   28 (  80 expanded)
%              Depth                    :   12
%              Number of atoms          :  116 ( 468 expanded)
%              Number of equality atoms :   17 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,(
    ! [A_50] :
      ( u1_struct_0(A_50) = k2_struct_0(A_50)
      | ~ l1_struct_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = k2_struct_0(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_61,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_57])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_40])).

tff(c_89,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_101,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_89])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_36,plain,(
    v4_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_32,plain,(
    '#skF_5' = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    ~ v4_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    ~ v4_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_67,plain,(
    ! [B_52,A_53] :
      ( l1_pre_topc(B_52)
      | ~ m1_pre_topc(B_52,A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_70,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_67])).

tff(c_73,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_70])).

tff(c_56,plain,(
    ! [A_11] :
      ( u1_struct_0(A_11) = k2_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_52])).

tff(c_77,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_73,c_56])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_79,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_43])).

tff(c_99,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_79,c_89])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_99,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    ! [A_63,B_64,C_65] :
      ( k9_subset_1(A_63,B_64,C_65) = k3_xboole_0(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_170,plain,(
    ! [B_68,B_69,A_70] :
      ( k9_subset_1(B_68,B_69,A_70) = k3_xboole_0(B_69,A_70)
      | ~ r1_tarski(A_70,B_68) ) ),
    inference(resolution,[status(thm)],[c_14,c_142])).

tff(c_181,plain,(
    ! [B_2,B_69] : k9_subset_1(B_2,B_69,B_2) = k3_xboole_0(B_69,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_405,plain,(
    ! [B_116,D_117,A_118] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_116),D_117,k2_struct_0(B_116)),B_116)
      | ~ v4_pre_topc(D_117,A_118)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_116),D_117,k2_struct_0(B_116)),k1_zfmisc_1(u1_struct_0(B_116)))
      | ~ m1_pre_topc(B_116,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_556,plain,(
    ! [B_134,A_135,A_136] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(B_134),A_135,k2_struct_0(B_134)),B_134)
      | ~ v4_pre_topc(A_135,A_136)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_134),A_135,k2_struct_0(B_134)),k1_zfmisc_1(u1_struct_0(B_134)))
      | ~ m1_pre_topc(B_134,A_136)
      | ~ l1_pre_topc(A_136)
      | ~ r1_tarski(A_135,u1_struct_0(A_136)) ) ),
    inference(resolution,[status(thm)],[c_14,c_405])).

tff(c_560,plain,(
    ! [A_135,A_136] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),A_135,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_135,A_136)
      | ~ m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'),A_135,k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_136)
      | ~ l1_pre_topc(A_136)
      | ~ r1_tarski(A_135,u1_struct_0(A_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_556])).

tff(c_991,plain,(
    ! [A_195,A_196] :
      ( v4_pre_topc(k3_xboole_0(A_195,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc(A_195,A_196)
      | ~ m1_subset_1(k3_xboole_0(A_195,k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_196)
      | ~ l1_pre_topc(A_196)
      | ~ r1_tarski(A_195,u1_struct_0(A_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_77,c_181,c_77,c_560])).

tff(c_997,plain,(
    ! [A_196] :
      ( v4_pre_topc(k3_xboole_0('#skF_3',k2_struct_0('#skF_4')),'#skF_4')
      | ~ v4_pre_topc('#skF_3',A_196)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4',A_196)
      | ~ l1_pre_topc(A_196)
      | ~ r1_tarski('#skF_3',u1_struct_0(A_196)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_991])).

tff(c_1005,plain,(
    ! [A_196] :
      ( v4_pre_topc('#skF_3','#skF_4')
      | ~ v4_pre_topc('#skF_3',A_196)
      | ~ m1_pre_topc('#skF_4',A_196)
      | ~ l1_pre_topc(A_196)
      | ~ r1_tarski('#skF_3',u1_struct_0(A_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_114,c_997])).

tff(c_1009,plain,(
    ! [A_197] :
      ( ~ v4_pre_topc('#skF_3',A_197)
      | ~ m1_pre_topc('#skF_4',A_197)
      | ~ l1_pre_topc(A_197)
      | ~ r1_tarski('#skF_3',u1_struct_0(A_197)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1005])).

tff(c_1015,plain,
    ( ~ v4_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_1009])).

tff(c_1020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_42,c_38,c_36,c_1015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:33:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.55  
% 3.53/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.55  %$ v4_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.53/1.55  
% 3.53/1.55  %Foreground sorts:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Background operators:
% 3.53/1.55  
% 3.53/1.55  
% 3.53/1.55  %Foreground operators:
% 3.53/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.53/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.53/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.55  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.53/1.55  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.53/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.55  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.53/1.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.53/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.55  
% 3.53/1.57  tff(f_93, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v4_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v4_pre_topc(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 3.53/1.57  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.53/1.57  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.53/1.57  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.53/1.57  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.53/1.57  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.53/1.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.57  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.53/1.57  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v4_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v4_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_pre_topc)).
% 3.53/1.57  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.57  tff(c_18, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.53/1.57  tff(c_52, plain, (![A_50]: (u1_struct_0(A_50)=k2_struct_0(A_50) | ~l1_struct_0(A_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.53/1.57  tff(c_57, plain, (![A_51]: (u1_struct_0(A_51)=k2_struct_0(A_51) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_18, c_52])).
% 3.53/1.57  tff(c_61, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_57])).
% 3.53/1.57  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.57  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_40])).
% 3.53/1.57  tff(c_89, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.53/1.57  tff(c_101, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_89])).
% 3.53/1.57  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.57  tff(c_36, plain, (v4_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.57  tff(c_32, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.57  tff(c_30, plain, (~v4_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.57  tff(c_44, plain, (~v4_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 3.53/1.57  tff(c_67, plain, (![B_52, A_53]: (l1_pre_topc(B_52) | ~m1_pre_topc(B_52, A_53) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.53/1.57  tff(c_70, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_67])).
% 3.53/1.57  tff(c_73, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_70])).
% 3.53/1.57  tff(c_56, plain, (![A_11]: (u1_struct_0(A_11)=k2_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_18, c_52])).
% 3.53/1.57  tff(c_77, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_73, c_56])).
% 3.53/1.57  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.53/1.57  tff(c_43, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.53/1.57  tff(c_79, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_43])).
% 3.53/1.57  tff(c_99, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_79, c_89])).
% 3.53/1.57  tff(c_8, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.53/1.57  tff(c_114, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_99, c_8])).
% 3.53/1.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.53/1.57  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.53/1.57  tff(c_142, plain, (![A_63, B_64, C_65]: (k9_subset_1(A_63, B_64, C_65)=k3_xboole_0(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.53/1.57  tff(c_170, plain, (![B_68, B_69, A_70]: (k9_subset_1(B_68, B_69, A_70)=k3_xboole_0(B_69, A_70) | ~r1_tarski(A_70, B_68))), inference(resolution, [status(thm)], [c_14, c_142])).
% 3.53/1.57  tff(c_181, plain, (![B_2, B_69]: (k9_subset_1(B_2, B_69, B_2)=k3_xboole_0(B_69, B_2))), inference(resolution, [status(thm)], [c_6, c_170])).
% 3.53/1.57  tff(c_405, plain, (![B_116, D_117, A_118]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_116), D_117, k2_struct_0(B_116)), B_116) | ~v4_pre_topc(D_117, A_118) | ~m1_subset_1(D_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_116), D_117, k2_struct_0(B_116)), k1_zfmisc_1(u1_struct_0(B_116))) | ~m1_pre_topc(B_116, A_118) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.53/1.57  tff(c_556, plain, (![B_134, A_135, A_136]: (v4_pre_topc(k9_subset_1(u1_struct_0(B_134), A_135, k2_struct_0(B_134)), B_134) | ~v4_pre_topc(A_135, A_136) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_134), A_135, k2_struct_0(B_134)), k1_zfmisc_1(u1_struct_0(B_134))) | ~m1_pre_topc(B_134, A_136) | ~l1_pre_topc(A_136) | ~r1_tarski(A_135, u1_struct_0(A_136)))), inference(resolution, [status(thm)], [c_14, c_405])).
% 3.53/1.57  tff(c_560, plain, (![A_135, A_136]: (v4_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), A_135, k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc(A_135, A_136) | ~m1_subset_1(k9_subset_1(k2_struct_0('#skF_4'), A_135, k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_136) | ~l1_pre_topc(A_136) | ~r1_tarski(A_135, u1_struct_0(A_136)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_556])).
% 3.53/1.57  tff(c_991, plain, (![A_195, A_196]: (v4_pre_topc(k3_xboole_0(A_195, k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc(A_195, A_196) | ~m1_subset_1(k3_xboole_0(A_195, k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_196) | ~l1_pre_topc(A_196) | ~r1_tarski(A_195, u1_struct_0(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_77, c_181, c_77, c_560])).
% 3.53/1.57  tff(c_997, plain, (![A_196]: (v4_pre_topc(k3_xboole_0('#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v4_pre_topc('#skF_3', A_196) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', A_196) | ~l1_pre_topc(A_196) | ~r1_tarski('#skF_3', u1_struct_0(A_196)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_991])).
% 3.53/1.57  tff(c_1005, plain, (![A_196]: (v4_pre_topc('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_3', A_196) | ~m1_pre_topc('#skF_4', A_196) | ~l1_pre_topc(A_196) | ~r1_tarski('#skF_3', u1_struct_0(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_114, c_997])).
% 3.53/1.57  tff(c_1009, plain, (![A_197]: (~v4_pre_topc('#skF_3', A_197) | ~m1_pre_topc('#skF_4', A_197) | ~l1_pre_topc(A_197) | ~r1_tarski('#skF_3', u1_struct_0(A_197)))), inference(negUnitSimplification, [status(thm)], [c_44, c_1005])).
% 3.53/1.57  tff(c_1015, plain, (~v4_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_61, c_1009])).
% 3.53/1.57  tff(c_1020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_42, c_38, c_36, c_1015])).
% 3.53/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.57  
% 3.53/1.57  Inference rules
% 3.53/1.57  ----------------------
% 3.53/1.57  #Ref     : 0
% 3.53/1.57  #Sup     : 225
% 3.53/1.57  #Fact    : 0
% 3.53/1.57  #Define  : 0
% 3.53/1.57  #Split   : 7
% 3.53/1.57  #Chain   : 0
% 3.53/1.57  #Close   : 0
% 3.53/1.57  
% 3.53/1.57  Ordering : KBO
% 3.53/1.57  
% 3.53/1.57  Simplification rules
% 3.53/1.57  ----------------------
% 3.53/1.57  #Subsume      : 43
% 3.53/1.57  #Demod        : 142
% 3.53/1.57  #Tautology    : 74
% 3.53/1.57  #SimpNegUnit  : 3
% 3.53/1.57  #BackRed      : 2
% 3.53/1.57  
% 3.53/1.57  #Partial instantiations: 0
% 3.53/1.57  #Strategies tried      : 1
% 3.53/1.57  
% 3.53/1.57  Timing (in seconds)
% 3.53/1.57  ----------------------
% 3.53/1.57  Preprocessing        : 0.31
% 3.53/1.57  Parsing              : 0.16
% 3.53/1.57  CNF conversion       : 0.02
% 3.53/1.57  Main loop            : 0.50
% 3.53/1.57  Inferencing          : 0.19
% 3.53/1.57  Reduction            : 0.15
% 3.53/1.57  Demodulation         : 0.11
% 3.53/1.57  BG Simplification    : 0.02
% 3.53/1.57  Subsumption          : 0.10
% 3.53/1.57  Abstraction          : 0.03
% 3.53/1.57  MUC search           : 0.00
% 3.53/1.57  Cooper               : 0.00
% 3.53/1.57  Total                : 0.84
% 3.53/1.57  Index Insertion      : 0.00
% 3.53/1.57  Index Deletion       : 0.00
% 3.53/1.57  Index Matching       : 0.00
% 3.53/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

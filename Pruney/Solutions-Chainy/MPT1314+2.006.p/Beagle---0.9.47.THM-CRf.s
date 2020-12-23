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
% DateTime   : Thu Dec  3 10:23:00 EST 2020

% Result     : Theorem 11.36s
% Output     : CNFRefutation 11.36s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 280 expanded)
%              Number of leaves         :   29 ( 110 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 678 expanded)
%              Number of equality atoms :   21 ( 123 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
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

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_47,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_79,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    ~ v3_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,(
    ~ v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_42,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_99,plain,(
    ! [B_61,A_62] :
      ( l1_pre_topc(B_61)
      | ~ m1_pre_topc(B_61,A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_99])).

tff(c_105,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_102])).

tff(c_18,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83,plain,(
    ! [A_57] :
      ( u1_struct_0(A_57) = k2_struct_0(A_57)
      | ~ l1_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_110,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_87])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_43,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_111,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_43])).

tff(c_116,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(A_65,B_66)
      | ~ m1_subset_1(A_65,k1_zfmisc_1(B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_126,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_111,c_116])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_132,plain,(
    k3_xboole_0('#skF_3',k2_struct_0('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_126,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_58] :
      ( u1_struct_0(A_58) = k2_struct_0(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_92,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_88])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_93,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40])).

tff(c_128,plain,(
    r1_tarski('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_93,c_116])).

tff(c_36,plain,(
    v3_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_150,plain,(
    ! [A_70,B_71,C_72] :
      ( k9_subset_1(A_70,B_71,C_72) = k3_xboole_0(B_71,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_160,plain,(
    ! [B_71] : k9_subset_1(k2_struct_0('#skF_4'),B_71,'#skF_3') = k3_xboole_0(B_71,'#skF_3') ),
    inference(resolution,[status(thm)],[c_111,c_150])).

tff(c_292,plain,(
    ! [A_81,C_82,B_83] :
      ( k9_subset_1(A_81,C_82,B_83) = k9_subset_1(A_81,B_83,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_300,plain,(
    ! [B_83] : k9_subset_1(k2_struct_0('#skF_4'),B_83,'#skF_3') = k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_83) ),
    inference(resolution,[status(thm)],[c_111,c_292])).

tff(c_309,plain,(
    ! [B_83] : k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',B_83) = k3_xboole_0(B_83,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_300])).

tff(c_14,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1046,plain,(
    ! [B_115,D_116,A_117] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_115),D_116,k2_struct_0(B_115)),B_115)
      | ~ v3_pre_topc(D_116,A_117)
      | ~ m1_subset_1(D_116,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_115),D_116,k2_struct_0(B_115)),k1_zfmisc_1(u1_struct_0(B_115)))
      | ~ m1_pre_topc(B_115,A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5122,plain,(
    ! [B_234,A_235,A_236] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_234),A_235,k2_struct_0(B_234)),B_234)
      | ~ v3_pre_topc(A_235,A_236)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(B_234),A_235,k2_struct_0(B_234)),k1_zfmisc_1(u1_struct_0(B_234)))
      | ~ m1_pre_topc(B_234,A_236)
      | ~ l1_pre_topc(A_236)
      | ~ r1_tarski(A_235,u1_struct_0(A_236)) ) ),
    inference(resolution,[status(thm)],[c_14,c_1046])).

tff(c_19131,plain,(
    ! [B_429,A_430,A_431] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(B_429),A_430,k2_struct_0(B_429)),B_429)
      | ~ v3_pre_topc(A_430,A_431)
      | ~ m1_pre_topc(B_429,A_431)
      | ~ l1_pre_topc(A_431)
      | ~ r1_tarski(A_430,u1_struct_0(A_431))
      | ~ r1_tarski(k9_subset_1(u1_struct_0(B_429),A_430,k2_struct_0(B_429)),u1_struct_0(B_429)) ) ),
    inference(resolution,[status(thm)],[c_14,c_5122])).

tff(c_19133,plain,(
    ! [A_430] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'),A_430,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(A_430,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ r1_tarski(A_430,u1_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(u1_struct_0('#skF_4'),A_430,k2_struct_0('#skF_4')),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_38,c_19131])).

tff(c_20109,plain,(
    ! [A_438] :
      ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),A_438,k2_struct_0('#skF_4')),'#skF_4')
      | ~ v3_pre_topc(A_438,'#skF_2')
      | ~ r1_tarski(A_438,k2_struct_0('#skF_2'))
      | ~ r1_tarski(k9_subset_1(k2_struct_0('#skF_4'),A_438,k2_struct_0('#skF_4')),k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_92,c_42,c_110,c_19133])).

tff(c_20133,plain,
    ( v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'),'#skF_3',k2_struct_0('#skF_4')),'#skF_4')
    | ~ v3_pre_topc('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_3',k2_struct_0('#skF_2'))
    | ~ r1_tarski(k3_xboole_0(k2_struct_0('#skF_4'),'#skF_3'),k2_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_20109])).

tff(c_20140,plain,(
    v3_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_132,c_2,c_128,c_36,c_132,c_2,c_309,c_20133])).

tff(c_20142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_20140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.36/4.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.36/4.66  
% 11.36/4.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.36/4.66  %$ v3_pre_topc > r1_tarski > m1_subset_1 > m1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 11.36/4.66  
% 11.36/4.66  %Foreground sorts:
% 11.36/4.66  
% 11.36/4.66  
% 11.36/4.66  %Background operators:
% 11.36/4.66  
% 11.36/4.66  
% 11.36/4.66  %Foreground operators:
% 11.36/4.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.36/4.66  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 11.36/4.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.36/4.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.36/4.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.36/4.66  tff('#skF_5', type, '#skF_5': $i).
% 11.36/4.66  tff('#skF_2', type, '#skF_2': $i).
% 11.36/4.66  tff('#skF_3', type, '#skF_3': $i).
% 11.36/4.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.36/4.66  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.36/4.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.36/4.66  tff('#skF_4', type, '#skF_4': $i).
% 11.36/4.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.36/4.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 11.36/4.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.36/4.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.36/4.66  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 11.36/4.66  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.36/4.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.36/4.66  
% 11.36/4.68  tff(f_97, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 11.36/4.68  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 11.36/4.68  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.36/4.68  tff(f_51, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 11.36/4.68  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 11.36/4.68  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.36/4.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.36/4.68  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.36/4.68  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 11.36/4.68  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => (v3_pre_topc(C, B) <=> (?[D]: ((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & (k9_subset_1(u1_struct_0(B), D, k2_struct_0(B)) = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tops_2)).
% 11.36/4.68  tff(c_32, plain, ('#skF_5'='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.36/4.68  tff(c_30, plain, (~v3_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.36/4.68  tff(c_44, plain, (~v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30])).
% 11.36/4.68  tff(c_42, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.36/4.68  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.36/4.68  tff(c_99, plain, (![B_61, A_62]: (l1_pre_topc(B_61) | ~m1_pre_topc(B_61, A_62) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.36/4.68  tff(c_102, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_99])).
% 11.36/4.68  tff(c_105, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_102])).
% 11.36/4.68  tff(c_18, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.36/4.68  tff(c_83, plain, (![A_57]: (u1_struct_0(A_57)=k2_struct_0(A_57) | ~l1_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 11.36/4.68  tff(c_87, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(resolution, [status(thm)], [c_18, c_83])).
% 11.36/4.68  tff(c_110, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_105, c_87])).
% 11.36/4.68  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.36/4.68  tff(c_43, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 11.36/4.68  tff(c_111, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_43])).
% 11.36/4.68  tff(c_116, plain, (![A_65, B_66]: (r1_tarski(A_65, B_66) | ~m1_subset_1(A_65, k1_zfmisc_1(B_66)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.36/4.68  tff(c_126, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_111, c_116])).
% 11.36/4.68  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.36/4.68  tff(c_132, plain, (k3_xboole_0('#skF_3', k2_struct_0('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_126, c_4])).
% 11.36/4.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.36/4.68  tff(c_88, plain, (![A_58]: (u1_struct_0(A_58)=k2_struct_0(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_18, c_83])).
% 11.36/4.68  tff(c_92, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_88])).
% 11.36/4.68  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.36/4.68  tff(c_93, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_40])).
% 11.36/4.68  tff(c_128, plain, (r1_tarski('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_93, c_116])).
% 11.36/4.68  tff(c_36, plain, (v3_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.36/4.68  tff(c_150, plain, (![A_70, B_71, C_72]: (k9_subset_1(A_70, B_71, C_72)=k3_xboole_0(B_71, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.36/4.68  tff(c_160, plain, (![B_71]: (k9_subset_1(k2_struct_0('#skF_4'), B_71, '#skF_3')=k3_xboole_0(B_71, '#skF_3'))), inference(resolution, [status(thm)], [c_111, c_150])).
% 11.36/4.68  tff(c_292, plain, (![A_81, C_82, B_83]: (k9_subset_1(A_81, C_82, B_83)=k9_subset_1(A_81, B_83, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.36/4.68  tff(c_300, plain, (![B_83]: (k9_subset_1(k2_struct_0('#skF_4'), B_83, '#skF_3')=k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_83))), inference(resolution, [status(thm)], [c_111, c_292])).
% 11.36/4.68  tff(c_309, plain, (![B_83]: (k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', B_83)=k3_xboole_0(B_83, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_300])).
% 11.36/4.68  tff(c_14, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 11.36/4.68  tff(c_1046, plain, (![B_115, D_116, A_117]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_115), D_116, k2_struct_0(B_115)), B_115) | ~v3_pre_topc(D_116, A_117) | ~m1_subset_1(D_116, k1_zfmisc_1(u1_struct_0(A_117))) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_115), D_116, k2_struct_0(B_115)), k1_zfmisc_1(u1_struct_0(B_115))) | ~m1_pre_topc(B_115, A_117) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_79])).
% 11.36/4.68  tff(c_5122, plain, (![B_234, A_235, A_236]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_234), A_235, k2_struct_0(B_234)), B_234) | ~v3_pre_topc(A_235, A_236) | ~m1_subset_1(k9_subset_1(u1_struct_0(B_234), A_235, k2_struct_0(B_234)), k1_zfmisc_1(u1_struct_0(B_234))) | ~m1_pre_topc(B_234, A_236) | ~l1_pre_topc(A_236) | ~r1_tarski(A_235, u1_struct_0(A_236)))), inference(resolution, [status(thm)], [c_14, c_1046])).
% 11.36/4.68  tff(c_19131, plain, (![B_429, A_430, A_431]: (v3_pre_topc(k9_subset_1(u1_struct_0(B_429), A_430, k2_struct_0(B_429)), B_429) | ~v3_pre_topc(A_430, A_431) | ~m1_pre_topc(B_429, A_431) | ~l1_pre_topc(A_431) | ~r1_tarski(A_430, u1_struct_0(A_431)) | ~r1_tarski(k9_subset_1(u1_struct_0(B_429), A_430, k2_struct_0(B_429)), u1_struct_0(B_429)))), inference(resolution, [status(thm)], [c_14, c_5122])).
% 11.36/4.68  tff(c_19133, plain, (![A_430]: (v3_pre_topc(k9_subset_1(u1_struct_0('#skF_4'), A_430, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(A_430, '#skF_2') | ~l1_pre_topc('#skF_2') | ~r1_tarski(A_430, u1_struct_0('#skF_2')) | ~r1_tarski(k9_subset_1(u1_struct_0('#skF_4'), A_430, k2_struct_0('#skF_4')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_38, c_19131])).
% 11.36/4.68  tff(c_20109, plain, (![A_438]: (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), A_438, k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc(A_438, '#skF_2') | ~r1_tarski(A_438, k2_struct_0('#skF_2')) | ~r1_tarski(k9_subset_1(k2_struct_0('#skF_4'), A_438, k2_struct_0('#skF_4')), k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_92, c_42, c_110, c_19133])).
% 11.36/4.68  tff(c_20133, plain, (v3_pre_topc(k9_subset_1(k2_struct_0('#skF_4'), '#skF_3', k2_struct_0('#skF_4')), '#skF_4') | ~v3_pre_topc('#skF_3', '#skF_2') | ~r1_tarski('#skF_3', k2_struct_0('#skF_2')) | ~r1_tarski(k3_xboole_0(k2_struct_0('#skF_4'), '#skF_3'), k2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_309, c_20109])).
% 11.36/4.68  tff(c_20140, plain, (v3_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_132, c_2, c_128, c_36, c_132, c_2, c_309, c_20133])).
% 11.36/4.68  tff(c_20142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_20140])).
% 11.36/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.36/4.68  
% 11.36/4.68  Inference rules
% 11.36/4.68  ----------------------
% 11.36/4.68  #Ref     : 0
% 11.36/4.68  #Sup     : 4692
% 11.36/4.68  #Fact    : 0
% 11.36/4.68  #Define  : 0
% 11.36/4.68  #Split   : 2
% 11.36/4.68  #Chain   : 0
% 11.36/4.68  #Close   : 0
% 11.36/4.68  
% 11.36/4.68  Ordering : KBO
% 11.36/4.68  
% 11.36/4.68  Simplification rules
% 11.36/4.68  ----------------------
% 11.36/4.68  #Subsume      : 886
% 11.36/4.68  #Demod        : 4659
% 11.36/4.68  #Tautology    : 2124
% 11.36/4.68  #SimpNegUnit  : 1
% 11.36/4.68  #BackRed      : 2
% 11.36/4.68  
% 11.36/4.68  #Partial instantiations: 0
% 11.36/4.68  #Strategies tried      : 1
% 11.36/4.68  
% 11.36/4.68  Timing (in seconds)
% 11.36/4.68  ----------------------
% 11.36/4.68  Preprocessing        : 0.33
% 11.36/4.68  Parsing              : 0.18
% 11.36/4.68  CNF conversion       : 0.02
% 11.36/4.68  Main loop            : 3.56
% 11.36/4.68  Inferencing          : 0.80
% 11.36/4.68  Reduction            : 2.03
% 11.36/4.68  Demodulation         : 1.82
% 11.36/4.68  BG Simplification    : 0.11
% 11.36/4.68  Subsumption          : 0.49
% 11.36/4.68  Abstraction          : 0.16
% 11.36/4.68  MUC search           : 0.00
% 11.36/4.68  Cooper               : 0.00
% 11.36/4.68  Total                : 3.92
% 11.36/4.68  Index Insertion      : 0.00
% 11.36/4.68  Index Deletion       : 0.00
% 11.36/4.68  Index Matching       : 0.00
% 11.36/4.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------

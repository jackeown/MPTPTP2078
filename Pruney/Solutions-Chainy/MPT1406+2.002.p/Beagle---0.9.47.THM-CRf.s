%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:34 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 219 expanded)
%              Number of leaves         :   23 (  87 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 541 expanded)
%              Number of equality atoms :    8 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m2_connsp_2,type,(
    m2_connsp_2: ( $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m2_connsp_2(C,A,B)
               => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ! [C] :
          ( m2_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m2_connsp_2(C,A,B)
              <=> r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

tff(c_16,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k1_tops_1(A_33,B_34),B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_74,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_77,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_74])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_77,c_6])).

tff(c_112,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_81])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_18,plain,(
    m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_120,plain,(
    ! [C_39,A_40,B_41] :
      ( m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m2_connsp_2(C_39,A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_120])).

tff(c_125,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_122])).

tff(c_8,plain,(
    ! [A_8,B_10] :
      ( r1_tarski(k1_tops_1(A_8,B_10),B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_127,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_125,c_8])).

tff(c_130,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_127])).

tff(c_61,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(k3_xboole_0(A_30,C_31),B_32)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_242,plain,(
    ! [A_47,C_48,B_49] :
      ( k3_xboole_0(k3_xboole_0(A_47,C_48),B_49) = k3_xboole_0(A_47,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(resolution,[status(thm)],[c_61,c_6])).

tff(c_70,plain,(
    ! [A_1,B_2,B_32] :
      ( r1_tarski(k3_xboole_0(A_1,B_2),B_32)
      | ~ r1_tarski(B_2,B_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_581,plain,(
    ! [A_62,C_63,B_64,B_65] :
      ( r1_tarski(k3_xboole_0(A_62,C_63),B_64)
      | ~ r1_tarski(B_65,B_64)
      | ~ r1_tarski(A_62,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_70])).

tff(c_667,plain,(
    ! [A_73,C_74] :
      ( r1_tarski(k3_xboole_0(A_73,C_74),'#skF_3')
      | ~ r1_tarski(A_73,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_130,c_581])).

tff(c_696,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_3')
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_667])).

tff(c_794,plain,(
    ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_696])).

tff(c_472,plain,(
    ! [B_56,A_57,C_58] :
      ( r1_tarski(B_56,k1_tops_1(A_57,C_58))
      | ~ m2_connsp_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_474,plain,(
    ! [B_56] :
      ( r1_tarski(B_56,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_125,c_472])).

tff(c_1361,plain,(
    ! [B_96] :
      ( r1_tarski(B_96,k1_tops_1('#skF_1','#skF_3'))
      | ~ m2_connsp_2('#skF_3','#skF_1',B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_474])).

tff(c_1367,plain,
    ( r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3'))
    | ~ m2_connsp_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_1361])).

tff(c_1371,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1367])).

tff(c_1373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_794,c_1371])).

tff(c_1375,plain,(
    r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_1394,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1375,c_6])).

tff(c_595,plain,(
    ! [A_62,C_63] :
      ( r1_tarski(k3_xboole_0(A_62,C_63),'#skF_3')
      | ~ r1_tarski(A_62,k1_tops_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_130,c_581])).

tff(c_1404,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2',k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_595])).

tff(c_1432,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1375,c_1404])).

tff(c_1434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1432])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:56:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.70  
% 3.36/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.70  %$ m2_connsp_2 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k3_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.36/1.70  
% 3.36/1.70  %Foreground sorts:
% 3.36/1.70  
% 3.36/1.70  
% 3.36/1.70  %Background operators:
% 3.36/1.70  
% 3.36/1.70  
% 3.36/1.70  %Foreground operators:
% 3.36/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.36/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.70  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.36/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.36/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.36/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.36/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.70  tff(m2_connsp_2, type, m2_connsp_2: ($i * $i * $i) > $o).
% 3.36/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.70  
% 3.61/1.71  tff(f_83, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m2_connsp_2(C, A, B) => r1_tarski(B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_connsp_2)).
% 3.61/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.61/1.71  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.61/1.71  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.61/1.71  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m2_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 3.61/1.71  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.61/1.71  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m2_connsp_2(C, A, B) <=> r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_connsp_2)).
% 3.61/1.71  tff(c_16, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.61/1.71  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.71  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.71  tff(c_72, plain, (![A_33, B_34]: (r1_tarski(k1_tops_1(A_33, B_34), B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.61/1.71  tff(c_74, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_72])).
% 3.61/1.71  tff(c_77, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_74])).
% 3.61/1.71  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.61/1.71  tff(c_81, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_77, c_6])).
% 3.61/1.71  tff(c_112, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_81])).
% 3.61/1.71  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.71  tff(c_18, plain, (m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.61/1.71  tff(c_120, plain, (![C_39, A_40, B_41]: (m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_40))) | ~m2_connsp_2(C_39, A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.61/1.71  tff(c_122, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_120])).
% 3.61/1.71  tff(c_125, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_122])).
% 3.61/1.71  tff(c_8, plain, (![A_8, B_10]: (r1_tarski(k1_tops_1(A_8, B_10), B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.61/1.71  tff(c_127, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_125, c_8])).
% 3.61/1.71  tff(c_130, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_127])).
% 3.61/1.71  tff(c_61, plain, (![A_30, C_31, B_32]: (r1_tarski(k3_xboole_0(A_30, C_31), B_32) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.61/1.71  tff(c_242, plain, (![A_47, C_48, B_49]: (k3_xboole_0(k3_xboole_0(A_47, C_48), B_49)=k3_xboole_0(A_47, C_48) | ~r1_tarski(A_47, B_49))), inference(resolution, [status(thm)], [c_61, c_6])).
% 3.61/1.71  tff(c_70, plain, (![A_1, B_2, B_32]: (r1_tarski(k3_xboole_0(A_1, B_2), B_32) | ~r1_tarski(B_2, B_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_61])).
% 3.61/1.71  tff(c_581, plain, (![A_62, C_63, B_64, B_65]: (r1_tarski(k3_xboole_0(A_62, C_63), B_64) | ~r1_tarski(B_65, B_64) | ~r1_tarski(A_62, B_65))), inference(superposition, [status(thm), theory('equality')], [c_242, c_70])).
% 3.61/1.71  tff(c_667, plain, (![A_73, C_74]: (r1_tarski(k3_xboole_0(A_73, C_74), '#skF_3') | ~r1_tarski(A_73, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_130, c_581])).
% 3.61/1.71  tff(c_696, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_3') | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_112, c_667])).
% 3.61/1.71  tff(c_794, plain, (~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_696])).
% 3.61/1.71  tff(c_472, plain, (![B_56, A_57, C_58]: (r1_tarski(B_56, k1_tops_1(A_57, C_58)) | ~m2_connsp_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.61/1.71  tff(c_474, plain, (![B_56]: (r1_tarski(B_56, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_125, c_472])).
% 3.61/1.71  tff(c_1361, plain, (![B_96]: (r1_tarski(B_96, k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_474])).
% 3.61/1.71  tff(c_1367, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3')) | ~m2_connsp_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_20, c_1361])).
% 3.61/1.71  tff(c_1371, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1367])).
% 3.61/1.71  tff(c_1373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_794, c_1371])).
% 3.61/1.71  tff(c_1375, plain, (r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_696])).
% 3.61/1.71  tff(c_1394, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_1375, c_6])).
% 3.61/1.71  tff(c_595, plain, (![A_62, C_63]: (r1_tarski(k3_xboole_0(A_62, C_63), '#skF_3') | ~r1_tarski(A_62, k1_tops_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_130, c_581])).
% 3.61/1.71  tff(c_1404, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_595])).
% 3.61/1.71  tff(c_1432, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1375, c_1404])).
% 3.61/1.71  tff(c_1434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_1432])).
% 3.61/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.71  
% 3.61/1.71  Inference rules
% 3.61/1.71  ----------------------
% 3.61/1.71  #Ref     : 0
% 3.61/1.71  #Sup     : 401
% 3.61/1.71  #Fact    : 0
% 3.61/1.71  #Define  : 0
% 3.61/1.71  #Split   : 4
% 3.61/1.71  #Chain   : 0
% 3.61/1.71  #Close   : 0
% 3.61/1.71  
% 3.61/1.71  Ordering : KBO
% 3.61/1.71  
% 3.61/1.71  Simplification rules
% 3.61/1.71  ----------------------
% 3.61/1.71  #Subsume      : 67
% 3.61/1.71  #Demod        : 96
% 3.61/1.71  #Tautology    : 67
% 3.61/1.71  #SimpNegUnit  : 3
% 3.61/1.71  #BackRed      : 0
% 3.61/1.71  
% 3.61/1.71  #Partial instantiations: 0
% 3.61/1.71  #Strategies tried      : 1
% 3.61/1.71  
% 3.61/1.71  Timing (in seconds)
% 3.61/1.71  ----------------------
% 3.61/1.72  Preprocessing        : 0.32
% 3.61/1.72  Parsing              : 0.18
% 3.61/1.72  CNF conversion       : 0.02
% 3.61/1.72  Main loop            : 0.51
% 3.61/1.72  Inferencing          : 0.17
% 3.61/1.72  Reduction            : 0.17
% 3.61/1.72  Demodulation         : 0.13
% 3.61/1.72  BG Simplification    : 0.03
% 3.61/1.72  Subsumption          : 0.11
% 3.61/1.72  Abstraction          : 0.02
% 3.61/1.72  MUC search           : 0.00
% 3.61/1.72  Cooper               : 0.00
% 3.61/1.72  Total                : 0.86
% 3.61/1.72  Index Insertion      : 0.00
% 3.61/1.72  Index Deletion       : 0.00
% 3.61/1.72  Index Matching       : 0.00
% 3.61/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

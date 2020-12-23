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
% DateTime   : Thu Dec  3 10:20:24 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 193 expanded)
%              Number of leaves         :   25 (  77 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 367 expanded)
%              Number of equality atoms :   17 (  68 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(A),k2_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_pre_topc)).

tff(c_26,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_38,plain,(
    ! [A_18] :
      ( u1_struct_0(A_18) = k2_struct_0(A_18)
      | ~ l1_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [A_21] :
      ( u1_struct_0(A_21) = k2_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(resolution,[status(thm)],[c_22,c_38])).

tff(c_48,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_28,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_28])).

tff(c_55,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_49,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_34,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_34])).

tff(c_77,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_76])).

tff(c_78,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = k3_subset_1(A_26,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_28,B_29,C_30] :
      ( k7_subset_1(A_28,B_29,C_30) = k4_xboole_0(B_29,C_30)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_126,plain,(
    ! [B_35,A_36,C_37] :
      ( k7_subset_1(B_35,A_36,C_37) = k4_xboole_0(A_36,C_37)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_133,plain,(
    ! [B_2,C_37] : k7_subset_1(B_2,B_2,C_37) = k4_xboole_0(B_2,C_37) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_184,plain,(
    ! [B_43,A_44] :
      ( v4_pre_topc(B_43,A_44)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(A_44),k2_struct_0(A_44),B_43),A_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_44)))
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_190,plain,(
    ! [B_43] :
      ( v4_pre_topc(B_43,'#skF_1')
      | ~ v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_43),'#skF_1')
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_184])).

tff(c_194,plain,(
    ! [B_45] :
      ( v4_pre_topc(B_45,'#skF_1')
      | ~ v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_45),'#skF_1')
      | ~ m1_subset_1(B_45,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_48,c_133,c_190])).

tff(c_204,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_194])).

tff(c_210,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_77,c_204])).

tff(c_212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_210])).

tff(c_213,plain,(
    ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_214,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_237,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k3_subset_1(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_244,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_49,c_237])).

tff(c_260,plain,(
    ! [A_54,B_55,C_56] :
      ( k7_subset_1(A_54,B_55,C_56) = k4_xboole_0(B_55,C_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_285,plain,(
    ! [B_59,A_60,C_61] :
      ( k7_subset_1(B_59,A_60,C_61) = k4_xboole_0(A_60,C_61)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(resolution,[status(thm)],[c_14,c_260])).

tff(c_292,plain,(
    ! [B_2,C_61] : k7_subset_1(B_2,B_2,C_61) = k4_xboole_0(B_2,C_61) ),
    inference(resolution,[status(thm)],[c_6,c_285])).

tff(c_343,plain,(
    ! [A_67,B_68] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(A_67),k2_struct_0(A_67),B_68),A_67)
      | ~ v4_pre_topc(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_349,plain,(
    ! [B_68] :
      ( v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_1'),B_68),'#skF_1')
      | ~ v4_pre_topc(B_68,'#skF_1')
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_343])).

tff(c_354,plain,(
    ! [B_69] :
      ( v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'),B_69),'#skF_1')
      | ~ v4_pre_topc(B_69,'#skF_1')
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_48,c_292,c_349])).

tff(c_364,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_354])).

tff(c_370,plain,(
    v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_214,c_364])).

tff(c_372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_213,c_370])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.28  %$ v4_pre_topc > v3_pre_topc > r1_tarski > m1_subset_1 > l1_struct_0 > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.06/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.28  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.06/1.28  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.06/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.06/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.28  
% 2.06/1.29  tff(f_70, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 2.06/1.29  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.06/1.29  tff(f_47, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.06/1.29  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.06/1.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.29  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.29  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.06/1.29  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k7_subset_1(u1_struct_0(A), k2_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_pre_topc)).
% 2.06/1.29  tff(c_26, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.29  tff(c_22, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.29  tff(c_38, plain, (![A_18]: (u1_struct_0(A_18)=k2_struct_0(A_18) | ~l1_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.29  tff(c_44, plain, (![A_21]: (u1_struct_0(A_21)=k2_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(resolution, [status(thm)], [c_22, c_38])).
% 2.06/1.29  tff(c_48, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.06/1.29  tff(c_28, plain, (~v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.29  tff(c_54, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_28])).
% 2.06/1.29  tff(c_55, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 2.06/1.29  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.29  tff(c_49, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 2.06/1.29  tff(c_34, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.29  tff(c_76, plain, (v4_pre_topc('#skF_2', '#skF_1') | v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_34])).
% 2.06/1.29  tff(c_77, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_55, c_76])).
% 2.06/1.29  tff(c_78, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=k3_subset_1(A_26, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.29  tff(c_85, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_49, c_78])).
% 2.06/1.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.29  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.29  tff(c_91, plain, (![A_28, B_29, C_30]: (k7_subset_1(A_28, B_29, C_30)=k4_xboole_0(B_29, C_30) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.29  tff(c_126, plain, (![B_35, A_36, C_37]: (k7_subset_1(B_35, A_36, C_37)=k4_xboole_0(A_36, C_37) | ~r1_tarski(A_36, B_35))), inference(resolution, [status(thm)], [c_14, c_91])).
% 2.06/1.29  tff(c_133, plain, (![B_2, C_37]: (k7_subset_1(B_2, B_2, C_37)=k4_xboole_0(B_2, C_37))), inference(resolution, [status(thm)], [c_6, c_126])).
% 2.06/1.29  tff(c_184, plain, (![B_43, A_44]: (v4_pre_topc(B_43, A_44) | ~v3_pre_topc(k7_subset_1(u1_struct_0(A_44), k2_struct_0(A_44), B_43), A_44) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_44))) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.29  tff(c_190, plain, (![B_43]: (v4_pre_topc(B_43, '#skF_1') | ~v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_43), '#skF_1') | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_184])).
% 2.06/1.29  tff(c_194, plain, (![B_45]: (v4_pre_topc(B_45, '#skF_1') | ~v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_45), '#skF_1') | ~m1_subset_1(B_45, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_48, c_133, c_190])).
% 2.06/1.29  tff(c_204, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_85, c_194])).
% 2.06/1.29  tff(c_210, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_77, c_204])).
% 2.06/1.29  tff(c_212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_210])).
% 2.06/1.29  tff(c_213, plain, (~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 2.06/1.29  tff(c_214, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 2.06/1.29  tff(c_237, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k3_subset_1(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.29  tff(c_244, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_49, c_237])).
% 2.06/1.29  tff(c_260, plain, (![A_54, B_55, C_56]: (k7_subset_1(A_54, B_55, C_56)=k4_xboole_0(B_55, C_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.06/1.29  tff(c_285, plain, (![B_59, A_60, C_61]: (k7_subset_1(B_59, A_60, C_61)=k4_xboole_0(A_60, C_61) | ~r1_tarski(A_60, B_59))), inference(resolution, [status(thm)], [c_14, c_260])).
% 2.06/1.29  tff(c_292, plain, (![B_2, C_61]: (k7_subset_1(B_2, B_2, C_61)=k4_xboole_0(B_2, C_61))), inference(resolution, [status(thm)], [c_6, c_285])).
% 2.06/1.29  tff(c_343, plain, (![A_67, B_68]: (v3_pre_topc(k7_subset_1(u1_struct_0(A_67), k2_struct_0(A_67), B_68), A_67) | ~v4_pre_topc(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.29  tff(c_349, plain, (![B_68]: (v3_pre_topc(k7_subset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_1'), B_68), '#skF_1') | ~v4_pre_topc(B_68, '#skF_1') | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_343])).
% 2.06/1.29  tff(c_354, plain, (![B_69]: (v3_pre_topc(k4_xboole_0(k2_struct_0('#skF_1'), B_69), '#skF_1') | ~v4_pre_topc(B_69, '#skF_1') | ~m1_subset_1(B_69, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_48, c_292, c_349])).
% 2.06/1.29  tff(c_364, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_244, c_354])).
% 2.06/1.29  tff(c_370, plain, (v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_214, c_364])).
% 2.06/1.29  tff(c_372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_213, c_370])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 68
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 7
% 2.06/1.29  #Chain   : 0
% 2.06/1.29  #Close   : 0
% 2.06/1.29  
% 2.06/1.29  Ordering : KBO
% 2.06/1.29  
% 2.06/1.29  Simplification rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Subsume      : 2
% 2.06/1.29  #Demod        : 42
% 2.06/1.29  #Tautology    : 40
% 2.06/1.29  #SimpNegUnit  : 6
% 2.06/1.29  #BackRed      : 1
% 2.06/1.29  
% 2.06/1.29  #Partial instantiations: 0
% 2.06/1.29  #Strategies tried      : 1
% 2.06/1.29  
% 2.06/1.29  Timing (in seconds)
% 2.06/1.29  ----------------------
% 2.06/1.29  Preprocessing        : 0.30
% 2.06/1.29  Parsing              : 0.16
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.22
% 2.06/1.29  Inferencing          : 0.08
% 2.06/1.29  Reduction            : 0.07
% 2.06/1.29  Demodulation         : 0.05
% 2.06/1.29  BG Simplification    : 0.01
% 2.06/1.29  Subsumption          : 0.03
% 2.06/1.29  Abstraction          : 0.01
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.55
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

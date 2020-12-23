%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   60 (  70 expanded)
%              Number of leaves         :   33 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 (  82 expanded)
%              Number of equality atoms :   27 (  32 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_71,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_36,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_44,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_73,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_33,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_22,plain,(
    ! [A_13] : l1_orders_2(k2_yellow_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    ! [A_15] : u1_struct_0(k2_yellow_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_105,plain,(
    ! [A_31] :
      ( u1_struct_0(A_31) = k2_struct_0(A_31)
      | ~ l1_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_124,plain,(
    ! [A_34] :
      ( u1_struct_0(A_34) = k2_struct_0(A_34)
      | ~ l1_orders_2(A_34) ) ),
    inference(resolution,[status(thm)],[c_18,c_105])).

tff(c_130,plain,(
    ! [A_13] : u1_struct_0(k2_yellow_1(A_13)) = k2_struct_0(k2_yellow_1(A_13)) ),
    inference(resolution,[status(thm)],[c_22,c_124])).

tff(c_134,plain,(
    ! [A_13] : k2_struct_0(k2_yellow_1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_130])).

tff(c_147,plain,(
    ! [A_36] :
      ( m1_subset_1(k2_struct_0(A_36),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_156,plain,(
    ! [A_15] :
      ( m1_subset_1(k2_struct_0(k2_yellow_1(A_15)),k1_zfmisc_1(A_15))
      | ~ l1_struct_0(k2_yellow_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_147])).

tff(c_158,plain,(
    ! [A_15] :
      ( m1_subset_1(A_15,k1_zfmisc_1(A_15))
      | ~ l1_struct_0(k2_yellow_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_156])).

tff(c_8,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_9] : k9_setfam_1(A_9) = k1_zfmisc_1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_16] : k2_yellow_1(k9_setfam_1(A_16)) = k3_yellow_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_33,plain,(
    ! [A_16] : k2_yellow_1(k1_zfmisc_1(A_16)) = k3_yellow_1(A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30])).

tff(c_6,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    ! [A_41] :
      ( k4_yellow_0(k2_yellow_1(A_41)) = k3_tarski(A_41)
      | ~ r2_hidden(k3_tarski(A_41),A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_186,plain,(
    ! [A_5] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5))) = k3_tarski(k1_zfmisc_1(A_5))
      | ~ r2_hidden(A_5,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_179])).

tff(c_188,plain,(
    ! [A_5] :
      ( k4_yellow_0(k3_yellow_1(A_5)) = A_5
      | ~ r2_hidden(A_5,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_6,c_186])).

tff(c_190,plain,(
    ! [A_42] :
      ( k4_yellow_0(k3_yellow_1(A_42)) = A_42
      | ~ r2_hidden(A_42,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_188])).

tff(c_194,plain,(
    ! [A_7] :
      ( k4_yellow_0(k3_yellow_1(A_7)) = A_7
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ m1_subset_1(A_7,k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_10,c_190])).

tff(c_198,plain,(
    ! [A_43] :
      ( k4_yellow_0(k3_yellow_1(A_43)) = A_43
      | ~ m1_subset_1(A_43,k1_zfmisc_1(A_43)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_194])).

tff(c_203,plain,(
    ! [A_44] :
      ( k4_yellow_0(k3_yellow_1(A_44)) = A_44
      | ~ l1_struct_0(k2_yellow_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_158,c_198])).

tff(c_209,plain,(
    ! [A_44] :
      ( k4_yellow_0(k3_yellow_1(A_44)) = A_44
      | ~ l1_orders_2(k2_yellow_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_18,c_203])).

tff(c_212,plain,(
    ! [A_44] : k4_yellow_0(k3_yellow_1(A_44)) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_209])).

tff(c_32,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.33  
% 2.11/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.33  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > #nlpp > u1_struct_0 > u1_orders_2 > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k2_struct_0 > k1_zfmisc_1 > k1_yellow_1 > #skF_1 > #skF_2
% 2.11/1.33  
% 2.11/1.33  %Foreground sorts:
% 2.11/1.33  
% 2.11/1.33  
% 2.11/1.33  %Background operators:
% 2.11/1.33  
% 2.11/1.33  
% 2.11/1.33  %Foreground operators:
% 2.11/1.33  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.11/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.33  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.11/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.33  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.11/1.33  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.11/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.11/1.33  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.11/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.33  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.11/1.33  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.11/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.33  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.11/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.11/1.33  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.11/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.33  
% 2.11/1.34  tff(f_60, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.11/1.34  tff(f_56, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 2.11/1.34  tff(f_71, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.11/1.34  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.11/1.34  tff(f_52, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 2.11/1.34  tff(f_36, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.11/1.34  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.11/1.34  tff(f_44, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.11/1.34  tff(f_73, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.11/1.34  tff(f_33, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.11/1.34  tff(f_67, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.11/1.34  tff(f_76, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.11/1.34  tff(c_22, plain, (![A_13]: (l1_orders_2(k2_yellow_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.34  tff(c_18, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.34  tff(c_26, plain, (![A_15]: (u1_struct_0(k2_yellow_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.34  tff(c_105, plain, (![A_31]: (u1_struct_0(A_31)=k2_struct_0(A_31) | ~l1_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.11/1.34  tff(c_124, plain, (![A_34]: (u1_struct_0(A_34)=k2_struct_0(A_34) | ~l1_orders_2(A_34))), inference(resolution, [status(thm)], [c_18, c_105])).
% 2.11/1.34  tff(c_130, plain, (![A_13]: (u1_struct_0(k2_yellow_1(A_13))=k2_struct_0(k2_yellow_1(A_13)))), inference(resolution, [status(thm)], [c_22, c_124])).
% 2.11/1.34  tff(c_134, plain, (![A_13]: (k2_struct_0(k2_yellow_1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_130])).
% 2.11/1.34  tff(c_147, plain, (![A_36]: (m1_subset_1(k2_struct_0(A_36), k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.34  tff(c_156, plain, (![A_15]: (m1_subset_1(k2_struct_0(k2_yellow_1(A_15)), k1_zfmisc_1(A_15)) | ~l1_struct_0(k2_yellow_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_147])).
% 2.11/1.34  tff(c_158, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)) | ~l1_struct_0(k2_yellow_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_156])).
% 2.11/1.34  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.11/1.34  tff(c_10, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.11/1.34  tff(c_12, plain, (![A_9]: (k9_setfam_1(A_9)=k1_zfmisc_1(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.11/1.34  tff(c_30, plain, (![A_16]: (k2_yellow_1(k9_setfam_1(A_16))=k3_yellow_1(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.11/1.34  tff(c_33, plain, (![A_16]: (k2_yellow_1(k1_zfmisc_1(A_16))=k3_yellow_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30])).
% 2.11/1.34  tff(c_6, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.34  tff(c_179, plain, (![A_41]: (k4_yellow_0(k2_yellow_1(A_41))=k3_tarski(A_41) | ~r2_hidden(k3_tarski(A_41), A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.11/1.34  tff(c_186, plain, (![A_5]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_5)))=k3_tarski(k1_zfmisc_1(A_5)) | ~r2_hidden(A_5, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_179])).
% 2.11/1.34  tff(c_188, plain, (![A_5]: (k4_yellow_0(k3_yellow_1(A_5))=A_5 | ~r2_hidden(A_5, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_6, c_186])).
% 2.11/1.34  tff(c_190, plain, (![A_42]: (k4_yellow_0(k3_yellow_1(A_42))=A_42 | ~r2_hidden(A_42, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_8, c_188])).
% 2.11/1.34  tff(c_194, plain, (![A_7]: (k4_yellow_0(k3_yellow_1(A_7))=A_7 | v1_xboole_0(k1_zfmisc_1(A_7)) | ~m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_10, c_190])).
% 2.11/1.34  tff(c_198, plain, (![A_43]: (k4_yellow_0(k3_yellow_1(A_43))=A_43 | ~m1_subset_1(A_43, k1_zfmisc_1(A_43)))), inference(negUnitSimplification, [status(thm)], [c_8, c_194])).
% 2.11/1.34  tff(c_203, plain, (![A_44]: (k4_yellow_0(k3_yellow_1(A_44))=A_44 | ~l1_struct_0(k2_yellow_1(A_44)))), inference(resolution, [status(thm)], [c_158, c_198])).
% 2.11/1.34  tff(c_209, plain, (![A_44]: (k4_yellow_0(k3_yellow_1(A_44))=A_44 | ~l1_orders_2(k2_yellow_1(A_44)))), inference(resolution, [status(thm)], [c_18, c_203])).
% 2.11/1.34  tff(c_212, plain, (![A_44]: (k4_yellow_0(k3_yellow_1(A_44))=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_209])).
% 2.11/1.34  tff(c_32, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.11/1.34  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_212, c_32])).
% 2.11/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.34  
% 2.11/1.34  Inference rules
% 2.11/1.34  ----------------------
% 2.11/1.34  #Ref     : 0
% 2.11/1.34  #Sup     : 39
% 2.11/1.34  #Fact    : 0
% 2.11/1.34  #Define  : 0
% 2.11/1.34  #Split   : 0
% 2.11/1.34  #Chain   : 0
% 2.11/1.34  #Close   : 0
% 2.11/1.34  
% 2.11/1.34  Ordering : KBO
% 2.11/1.34  
% 2.11/1.34  Simplification rules
% 2.11/1.34  ----------------------
% 2.11/1.34  #Subsume      : 1
% 2.11/1.34  #Demod        : 15
% 2.11/1.34  #Tautology    : 24
% 2.11/1.34  #SimpNegUnit  : 2
% 2.11/1.34  #BackRed      : 1
% 2.11/1.34  
% 2.11/1.34  #Partial instantiations: 0
% 2.11/1.34  #Strategies tried      : 1
% 2.11/1.34  
% 2.11/1.34  Timing (in seconds)
% 2.11/1.34  ----------------------
% 2.11/1.35  Preprocessing        : 0.39
% 2.11/1.35  Parsing              : 0.22
% 2.11/1.35  CNF conversion       : 0.02
% 2.11/1.35  Main loop            : 0.15
% 2.11/1.35  Inferencing          : 0.06
% 2.11/1.35  Reduction            : 0.05
% 2.11/1.35  Demodulation         : 0.03
% 2.11/1.35  BG Simplification    : 0.01
% 2.11/1.35  Subsumption          : 0.02
% 2.11/1.35  Abstraction          : 0.01
% 2.11/1.35  MUC search           : 0.00
% 2.11/1.35  Cooper               : 0.00
% 2.11/1.35  Total                : 0.57
% 2.11/1.35  Index Insertion      : 0.00
% 2.11/1.35  Index Deletion       : 0.00
% 2.11/1.35  Index Matching       : 0.00
% 2.11/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

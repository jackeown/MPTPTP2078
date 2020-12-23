%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:34 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   57 (  60 expanded)
%              Number of leaves         :   34 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 (  79 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A)))))
         => k1_yellow_0(k2_yellow_1(u1_pre_topc(A)),B) = k3_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_118,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),A_36)
      | r1_tarski(k3_tarski(A_36),B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_27,B_28] : ~ r2_hidden(A_27,k2_zfmisc_1(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_124,plain,(
    ! [B_38] : r1_tarski(k3_tarski(k1_xboole_0),B_38) ),
    inference(resolution,[status(thm)],[c_118,c_90])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_24,plain,(
    ! [A_14] : l1_orders_2(k2_yellow_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    ! [A_30] :
      ( k1_yellow_0(A_30,k1_xboole_0) = k3_yellow_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    ! [A_14] : k1_yellow_0(k2_yellow_1(A_14),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_14)) ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_15] : u1_struct_0(k2_yellow_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_16,B_18] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_16)),B_18) = k3_tarski(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_16)))))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,(
    ! [A_43,B_44] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_43)),B_44) = k3_tarski(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(u1_pre_topc(A_43)))
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_150,plain,(
    ! [A_43] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_43)),k1_xboole_0) = k3_tarski(k1_xboole_0)
      | ~ l1_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_16,c_146])).

tff(c_153,plain,(
    ! [A_45] :
      ( k3_yellow_0(k2_yellow_1(u1_pre_topc(A_45))) = k1_xboole_0
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_96,c_150])).

tff(c_32,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_159,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_32])).

tff(c_166,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_159])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.17  
% 2.02/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.02/1.18  
% 2.02/1.18  %Foreground sorts:
% 2.02/1.18  
% 2.02/1.18  
% 2.02/1.18  %Background operators:
% 2.02/1.18  
% 2.02/1.18  
% 2.02/1.18  %Foreground operators:
% 2.02/1.18  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.02/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.02/1.18  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 2.02/1.18  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.02/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.18  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.02/1.18  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 2.02/1.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.02/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.18  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.02/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.18  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.02/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.02/1.18  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.02/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.02/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.02/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.18  
% 2.02/1.19  tff(f_87, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_1)).
% 2.02/1.19  tff(f_45, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.02/1.19  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.02/1.19  tff(f_38, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.02/1.19  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.02/1.19  tff(f_61, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.02/1.19  tff(f_57, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 2.02/1.19  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.02/1.19  tff(f_65, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.02/1.19  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) => (k1_yellow_0(k2_yellow_1(u1_pre_topc(A)), B) = k3_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow_1)).
% 2.02/1.19  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.02/1.19  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.02/1.19  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.02/1.19  tff(c_118, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), A_36) | r1_tarski(k3_tarski(A_36), B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.02/1.19  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.19  tff(c_84, plain, (![A_27, B_28]: (~r2_hidden(A_27, k2_zfmisc_1(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.19  tff(c_90, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_84])).
% 2.02/1.19  tff(c_124, plain, (![B_38]: (r1_tarski(k3_tarski(k1_xboole_0), B_38))), inference(resolution, [status(thm)], [c_118, c_90])).
% 2.02/1.19  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.02/1.19  tff(c_129, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_2])).
% 2.02/1.19  tff(c_24, plain, (![A_14]: (l1_orders_2(k2_yellow_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.02/1.19  tff(c_92, plain, (![A_30]: (k1_yellow_0(A_30, k1_xboole_0)=k3_yellow_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.02/1.19  tff(c_96, plain, (![A_14]: (k1_yellow_0(k2_yellow_1(A_14), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_14)))), inference(resolution, [status(thm)], [c_24, c_92])).
% 2.02/1.19  tff(c_16, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.02/1.19  tff(c_26, plain, (![A_15]: (u1_struct_0(k2_yellow_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.19  tff(c_30, plain, (![A_16, B_18]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_16)), B_18)=k3_tarski(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_16))))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.02/1.19  tff(c_146, plain, (![A_43, B_44]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_43)), B_44)=k3_tarski(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(u1_pre_topc(A_43))) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.02/1.19  tff(c_150, plain, (![A_43]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_43)), k1_xboole_0)=k3_tarski(k1_xboole_0) | ~l1_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(resolution, [status(thm)], [c_16, c_146])).
% 2.02/1.19  tff(c_153, plain, (![A_45]: (k3_yellow_0(k2_yellow_1(u1_pre_topc(A_45)))=k1_xboole_0 | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_96, c_150])).
% 2.02/1.19  tff(c_32, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.02/1.19  tff(c_159, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_153, c_32])).
% 2.02/1.19  tff(c_166, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_159])).
% 2.02/1.19  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_166])).
% 2.02/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.19  
% 2.02/1.19  Inference rules
% 2.02/1.19  ----------------------
% 2.02/1.19  #Ref     : 0
% 2.02/1.19  #Sup     : 27
% 2.02/1.19  #Fact    : 0
% 2.02/1.19  #Define  : 0
% 2.02/1.19  #Split   : 0
% 2.02/1.19  #Chain   : 0
% 2.02/1.19  #Close   : 0
% 2.02/1.19  
% 2.02/1.19  Ordering : KBO
% 2.02/1.19  
% 2.02/1.19  Simplification rules
% 2.02/1.19  ----------------------
% 2.02/1.19  #Subsume      : 2
% 2.02/1.19  #Demod        : 6
% 2.02/1.19  #Tautology    : 18
% 2.02/1.19  #SimpNegUnit  : 1
% 2.02/1.19  #BackRed      : 1
% 2.02/1.19  
% 2.02/1.19  #Partial instantiations: 0
% 2.02/1.19  #Strategies tried      : 1
% 2.02/1.19  
% 2.02/1.19  Timing (in seconds)
% 2.02/1.19  ----------------------
% 2.02/1.19  Preprocessing        : 0.31
% 2.02/1.19  Parsing              : 0.17
% 2.02/1.19  CNF conversion       : 0.02
% 2.02/1.19  Main loop            : 0.13
% 2.02/1.19  Inferencing          : 0.05
% 2.02/1.19  Reduction            : 0.04
% 2.02/1.19  Demodulation         : 0.03
% 2.02/1.19  BG Simplification    : 0.01
% 2.02/1.19  Subsumption          : 0.02
% 2.02/1.19  Abstraction          : 0.01
% 2.02/1.19  MUC search           : 0.00
% 2.02/1.19  Cooper               : 0.00
% 2.02/1.19  Total                : 0.47
% 2.02/1.19  Index Insertion      : 0.00
% 2.02/1.19  Index Deletion       : 0.00
% 2.02/1.19  Index Matching       : 0.00
% 2.02/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

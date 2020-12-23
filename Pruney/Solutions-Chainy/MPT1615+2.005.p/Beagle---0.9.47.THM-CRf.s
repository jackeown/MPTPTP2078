%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:34 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   53 (  56 expanded)
%              Number of leaves         :   32 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 (  78 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A)))))
         => k1_yellow_0(k2_yellow_1(u1_pre_topc(A)),B) = k3_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_1)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_32,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | k3_tarski(A_28) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_92,plain,(
    ! [A_32] :
      ( ~ r1_tarski(A_32,'#skF_1'(A_32))
      | k3_tarski(A_32) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_97,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_92])).

tff(c_20,plain,(
    ! [A_13] : l1_orders_2(k2_yellow_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    ! [A_27] :
      ( k1_yellow_0(A_27,k1_xboole_0) = k3_yellow_0(A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [A_13] : k1_yellow_0(k2_yellow_1(A_13),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_13)) ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ! [A_14] : u1_struct_0(k2_yellow_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_15,B_17] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_15)),B_17) = k3_tarski(B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_15)))))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_120,plain,(
    ! [A_38,B_39] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_38)),B_39) = k3_tarski(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(u1_pre_topc(A_38)))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_124,plain,(
    ! [A_38] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_38)),k1_xboole_0) = k3_tarski(k1_xboole_0)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_4,c_120])).

tff(c_127,plain,(
    ! [A_40] :
      ( k3_yellow_0(k2_yellow_1(u1_pre_topc(A_40))) = k1_xboole_0
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_72,c_124])).

tff(c_28,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_133,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_140,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_133])).

tff(c_142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:59:35 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.90/1.20  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.90/1.20  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 1.90/1.20  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.20  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.90/1.20  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.90/1.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.20  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.20  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.97/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.97/1.20  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.97/1.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.97/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.20  
% 1.97/1.21  tff(f_94, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_yellow_1)).
% 1.97/1.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.97/1.21  tff(f_60, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_orders_1)).
% 1.97/1.21  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.97/1.21  tff(f_68, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 1.97/1.21  tff(f_64, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 1.97/1.21  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.97/1.21  tff(f_72, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 1.97/1.21  tff(f_84, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) => (k1_yellow_0(k2_yellow_1(u1_pre_topc(A)), B) = k3_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow_1)).
% 1.97/1.21  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.21  tff(c_32, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.21  tff(c_30, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.21  tff(c_73, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | k3_tarski(A_28)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.97/1.21  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.97/1.21  tff(c_92, plain, (![A_32]: (~r1_tarski(A_32, '#skF_1'(A_32)) | k3_tarski(A_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_73, c_8])).
% 1.97/1.21  tff(c_97, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_92])).
% 1.97/1.21  tff(c_20, plain, (![A_13]: (l1_orders_2(k2_yellow_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.21  tff(c_68, plain, (![A_27]: (k1_yellow_0(A_27, k1_xboole_0)=k3_yellow_0(A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.21  tff(c_72, plain, (![A_13]: (k1_yellow_0(k2_yellow_1(A_13), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_13)))), inference(resolution, [status(thm)], [c_20, c_68])).
% 1.97/1.21  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.97/1.21  tff(c_22, plain, (![A_14]: (u1_struct_0(k2_yellow_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.97/1.21  tff(c_26, plain, (![A_15, B_17]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_15)), B_17)=k3_tarski(B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_15))))) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.97/1.21  tff(c_120, plain, (![A_38, B_39]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_38)), B_39)=k3_tarski(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(u1_pre_topc(A_38))) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 1.97/1.21  tff(c_124, plain, (![A_38]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_38)), k1_xboole_0)=k3_tarski(k1_xboole_0) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_4, c_120])).
% 1.97/1.21  tff(c_127, plain, (![A_40]: (k3_yellow_0(k2_yellow_1(u1_pre_topc(A_40)))=k1_xboole_0 | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_72, c_124])).
% 1.97/1.21  tff(c_28, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.97/1.21  tff(c_133, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_127, c_28])).
% 1.97/1.21  tff(c_140, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_133])).
% 1.97/1.21  tff(c_142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_140])).
% 1.97/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  Inference rules
% 1.97/1.21  ----------------------
% 1.97/1.21  #Ref     : 0
% 1.97/1.21  #Sup     : 22
% 1.97/1.21  #Fact    : 0
% 1.97/1.21  #Define  : 0
% 1.97/1.22  #Split   : 0
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 0
% 1.97/1.22  #Demod        : 6
% 1.97/1.22  #Tautology    : 15
% 1.97/1.22  #SimpNegUnit  : 1
% 1.97/1.22  #BackRed      : 0
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.22  Preprocessing        : 0.31
% 1.97/1.22  Parsing              : 0.17
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.13
% 1.97/1.22  Inferencing          : 0.05
% 1.97/1.22  Reduction            : 0.04
% 1.97/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.01
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.47
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

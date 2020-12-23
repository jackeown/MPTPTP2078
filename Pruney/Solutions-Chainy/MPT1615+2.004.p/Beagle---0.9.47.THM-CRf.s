%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:34 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   53 (  56 expanded)
%              Number of leaves         :   32 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 (  77 expanded)
%              Number of equality atoms :   23 (  26 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A)))))
         => k1_yellow_0(k2_yellow_1(u1_pre_topc(A)),B) = k3_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_1)).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_14] : l1_orders_2(k2_yellow_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_100,plain,(
    ! [A_30] :
      ( k1_yellow_0(A_30,k1_xboole_0) = k3_yellow_0(A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,(
    ! [A_14] : k1_yellow_0(k2_yellow_1(A_14),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_14)) ),
    inference(resolution,[status(thm)],[c_24,c_100])).

tff(c_105,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31),A_31)
      | k3_tarski(A_31) = k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_25,B_26] : ~ r2_hidden(A_25,k2_zfmisc_1(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_77,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_110,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_77])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26,plain,(
    ! [A_15] : u1_struct_0(k2_yellow_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_16,B_18] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_16)),B_18) = k3_tarski(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_16)))))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_152,plain,(
    ! [A_40,B_41] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_40)),B_41) = k3_tarski(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_pre_topc(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_156,plain,(
    ! [A_40] :
      ( k1_yellow_0(k2_yellow_1(u1_pre_topc(A_40)),k1_xboole_0) = k3_tarski(k1_xboole_0)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_159,plain,(
    ! [A_42] :
      ( k3_yellow_0(k2_yellow_1(u1_pre_topc(A_42))) = k1_xboole_0
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_110,c_156])).

tff(c_32,plain,(
    k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2'))) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_165,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_32])).

tff(c_172,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_165])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n012.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 18:15:22 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.17  %$ r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_orders_2 > l1_pre_topc > l1_orders_2 > k2_zfmisc_1 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_pre_topc > u1_orders_2 > k3_yellow_0 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 1.87/1.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.87/1.17  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 1.87/1.17  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.17  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.87/1.17  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.87/1.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 1.87/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.17  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.87/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.17  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 1.87/1.17  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 1.87/1.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.17  
% 2.14/1.18  tff(f_96, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (k3_yellow_0(k2_yellow_1(u1_pre_topc(A))) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_1)).
% 2.14/1.18  tff(f_70, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.14/1.18  tff(f_66, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 2.14/1.18  tff(f_62, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.14/1.18  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.14/1.18  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.14/1.18  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.14/1.18  tff(f_74, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.14/1.18  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A))))) => (k1_yellow_0(k2_yellow_1(u1_pre_topc(A)), B) = k3_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow_1)).
% 2.14/1.18  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.14/1.18  tff(c_36, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.14/1.18  tff(c_34, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.14/1.18  tff(c_24, plain, (![A_14]: (l1_orders_2(k2_yellow_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.18  tff(c_100, plain, (![A_30]: (k1_yellow_0(A_30, k1_xboole_0)=k3_yellow_0(A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.18  tff(c_104, plain, (![A_14]: (k1_yellow_0(k2_yellow_1(A_14), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_14)))), inference(resolution, [status(thm)], [c_24, c_100])).
% 2.14/1.18  tff(c_105, plain, (![A_31]: (r2_hidden('#skF_1'(A_31), A_31) | k3_tarski(A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.14/1.18  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.18  tff(c_74, plain, (![A_25, B_26]: (~r2_hidden(A_25, k2_zfmisc_1(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.14/1.18  tff(c_77, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_74])).
% 2.14/1.18  tff(c_110, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_105, c_77])).
% 2.14/1.18  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.14/1.18  tff(c_26, plain, (![A_15]: (u1_struct_0(k2_yellow_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.14/1.18  tff(c_30, plain, (![A_16, B_18]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_16)), B_18)=k3_tarski(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(A_16))))) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.14/1.18  tff(c_152, plain, (![A_40, B_41]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_40)), B_41)=k3_tarski(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_pre_topc(A_40))) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 2.14/1.18  tff(c_156, plain, (![A_40]: (k1_yellow_0(k2_yellow_1(u1_pre_topc(A_40)), k1_xboole_0)=k3_tarski(k1_xboole_0) | ~l1_pre_topc(A_40) | ~v2_pre_topc(A_40) | v2_struct_0(A_40))), inference(resolution, [status(thm)], [c_10, c_152])).
% 2.14/1.18  tff(c_159, plain, (![A_42]: (k3_yellow_0(k2_yellow_1(u1_pre_topc(A_42)))=k1_xboole_0 | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_110, c_156])).
% 2.14/1.18  tff(c_32, plain, (k3_yellow_0(k2_yellow_1(u1_pre_topc('#skF_2')))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.14/1.18  tff(c_165, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_159, c_32])).
% 2.14/1.18  tff(c_172, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_165])).
% 2.14/1.18  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_172])).
% 2.14/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.18  
% 2.14/1.18  Inference rules
% 2.14/1.18  ----------------------
% 2.14/1.18  #Ref     : 0
% 2.14/1.18  #Sup     : 30
% 2.14/1.18  #Fact    : 0
% 2.14/1.18  #Define  : 0
% 2.14/1.18  #Split   : 0
% 2.14/1.18  #Chain   : 0
% 2.14/1.18  #Close   : 0
% 2.14/1.18  
% 2.14/1.18  Ordering : KBO
% 2.14/1.18  
% 2.14/1.18  Simplification rules
% 2.14/1.18  ----------------------
% 2.14/1.18  #Subsume      : 2
% 2.14/1.18  #Demod        : 5
% 2.14/1.18  #Tautology    : 22
% 2.14/1.18  #SimpNegUnit  : 1
% 2.14/1.18  #BackRed      : 0
% 2.14/1.18  
% 2.14/1.18  #Partial instantiations: 0
% 2.14/1.18  #Strategies tried      : 1
% 2.14/1.18  
% 2.14/1.18  Timing (in seconds)
% 2.14/1.18  ----------------------
% 2.14/1.18  Preprocessing        : 0.31
% 2.14/1.18  Parsing              : 0.17
% 2.14/1.18  CNF conversion       : 0.02
% 2.14/1.18  Main loop            : 0.13
% 2.14/1.18  Inferencing          : 0.05
% 2.14/1.19  Reduction            : 0.04
% 2.14/1.19  Demodulation         : 0.03
% 2.14/1.19  BG Simplification    : 0.01
% 2.14/1.19  Subsumption          : 0.02
% 2.14/1.19  Abstraction          : 0.01
% 2.14/1.19  MUC search           : 0.00
% 2.14/1.19  Cooper               : 0.00
% 2.14/1.19  Total                : 0.47
% 2.14/1.19  Index Insertion      : 0.00
% 2.14/1.19  Index Deletion       : 0.00
% 2.14/1.19  Index Matching       : 0.00
% 2.14/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:55 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 101 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :  119 ( 319 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_82,plain,(
    ! [A_37,B_38,C_39] :
      ( k9_subset_1(A_37,B_38,C_39) = k3_xboole_0(B_38,C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    ! [B_38] : k9_subset_1(u1_struct_0('#skF_1'),B_38,'#skF_3') = k3_xboole_0(B_38,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_16,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_92,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_16])).

tff(c_93,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_18,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_108,plain,(
    ! [B_41,A_42] :
      ( v4_pre_topc(B_41,A_42)
      | ~ v2_compts_1(B_41,A_42)
      | ~ v8_pre_topc(A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_115,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_108])).

tff(c_122,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_18,c_115])).

tff(c_20,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_118,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_108])).

tff(c_125,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_22,c_20,c_118])).

tff(c_217,plain,(
    ! [B_48,C_49,A_50] :
      ( v4_pre_topc(k3_xboole_0(B_48,C_49),A_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v4_pre_topc(C_49,A_50)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ v4_pre_topc(B_48,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_232,plain,(
    ! [B_48] :
      ( v4_pre_topc(k3_xboole_0(B_48,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_48,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_217])).

tff(c_271,plain,(
    ! [B_53] :
      ( v4_pre_topc(k3_xboole_0(B_53,'#skF_2'),'#skF_1')
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_53,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_125,c_232])).

tff(c_290,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_271])).

tff(c_306,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_290])).

tff(c_94,plain,(
    ! [B_40] : k9_subset_1(u1_struct_0('#skF_1'),B_40,'#skF_3') = k3_xboole_0(B_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_subset_1(k9_subset_1(A_5,B_6,C_7),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [B_40] :
      ( m1_subset_1(k3_xboole_0(B_40,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_6])).

tff(c_140,plain,(
    ! [B_44] : m1_subset_1(k3_xboole_0(B_44,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_100])).

tff(c_149,plain,(
    ! [A_1] : m1_subset_1(k3_xboole_0('#skF_3',A_1),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_337,plain,(
    ! [C_57,A_58,B_59] :
      ( v2_compts_1(C_57,A_58)
      | ~ v4_pre_topc(C_57,A_58)
      | ~ r1_tarski(C_57,B_59)
      | ~ v2_compts_1(B_59,A_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_923,plain,(
    ! [A_93,B_94,A_95] :
      ( v2_compts_1(k3_xboole_0(A_93,B_94),A_95)
      | ~ v4_pre_topc(k3_xboole_0(A_93,B_94),A_95)
      | ~ v2_compts_1(A_93,A_95)
      | ~ m1_subset_1(k3_xboole_0(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(A_93,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95)
      | ~ v2_pre_topc(A_95) ) ),
    inference(resolution,[status(thm)],[c_4,c_337])).

tff(c_953,plain,(
    ! [A_1] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_149,c_923])).

tff(c_1099,plain,(
    ! [A_99] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_99),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_99),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_18,c_953])).

tff(c_1119,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_306,c_1099])).

tff(c_1146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:11:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.48  
% 3.29/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.48  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.29/1.48  
% 3.29/1.48  %Foreground sorts:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Background operators:
% 3.29/1.48  
% 3.29/1.48  
% 3.29/1.48  %Foreground operators:
% 3.29/1.48  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.29/1.48  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.29/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.29/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.29/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.29/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.48  
% 3.29/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.29/1.49  tff(f_101, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 3.29/1.49  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.29/1.49  tff(f_64, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 3.29/1.49  tff(f_51, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tops_1)).
% 3.29/1.49  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.29/1.49  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.29/1.49  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 3.29/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.49  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_82, plain, (![A_37, B_38, C_39]: (k9_subset_1(A_37, B_38, C_39)=k3_xboole_0(B_38, C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.29/1.49  tff(c_90, plain, (![B_38]: (k9_subset_1(u1_struct_0('#skF_1'), B_38, '#skF_3')=k3_xboole_0(B_38, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_82])).
% 3.29/1.49  tff(c_16, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_92, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_16])).
% 3.29/1.49  tff(c_93, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_92])).
% 3.29/1.49  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_22, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_18, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_108, plain, (![B_41, A_42]: (v4_pre_topc(B_41, A_42) | ~v2_compts_1(B_41, A_42) | ~v8_pre_topc(A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.29/1.49  tff(c_115, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_108])).
% 3.29/1.49  tff(c_122, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_18, c_115])).
% 3.29/1.49  tff(c_20, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.29/1.49  tff(c_118, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_108])).
% 3.29/1.49  tff(c_125, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_22, c_20, c_118])).
% 3.29/1.49  tff(c_217, plain, (![B_48, C_49, A_50]: (v4_pre_topc(k3_xboole_0(B_48, C_49), A_50) | ~m1_subset_1(C_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~v4_pre_topc(C_49, A_50) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_50))) | ~v4_pre_topc(B_48, A_50) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.49  tff(c_232, plain, (![B_48]: (v4_pre_topc(k3_xboole_0(B_48, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_48, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_217])).
% 3.29/1.49  tff(c_271, plain, (![B_53]: (v4_pre_topc(k3_xboole_0(B_53, '#skF_2'), '#skF_1') | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_53, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_125, c_232])).
% 3.29/1.49  tff(c_290, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_271])).
% 3.29/1.49  tff(c_306, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_290])).
% 3.29/1.49  tff(c_94, plain, (![B_40]: (k9_subset_1(u1_struct_0('#skF_1'), B_40, '#skF_3')=k3_xboole_0(B_40, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_82])).
% 3.29/1.49  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_subset_1(k9_subset_1(A_5, B_6, C_7), k1_zfmisc_1(A_5)) | ~m1_subset_1(C_7, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.49  tff(c_100, plain, (![B_40]: (m1_subset_1(k3_xboole_0(B_40, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_94, c_6])).
% 3.29/1.49  tff(c_140, plain, (![B_44]: (m1_subset_1(k3_xboole_0(B_44, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_100])).
% 3.29/1.49  tff(c_149, plain, (![A_1]: (m1_subset_1(k3_xboole_0('#skF_3', A_1), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_140])).
% 3.29/1.49  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.49  tff(c_337, plain, (![C_57, A_58, B_59]: (v2_compts_1(C_57, A_58) | ~v4_pre_topc(C_57, A_58) | ~r1_tarski(C_57, B_59) | ~v2_compts_1(B_59, A_58) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.29/1.49  tff(c_923, plain, (![A_93, B_94, A_95]: (v2_compts_1(k3_xboole_0(A_93, B_94), A_95) | ~v4_pre_topc(k3_xboole_0(A_93, B_94), A_95) | ~v2_compts_1(A_93, A_95) | ~m1_subset_1(k3_xboole_0(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(A_93, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95) | ~v2_pre_topc(A_95))), inference(resolution, [status(thm)], [c_4, c_337])).
% 3.29/1.49  tff(c_953, plain, (![A_1]: (v2_compts_1(k3_xboole_0('#skF_3', A_1), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_1), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_149, c_923])).
% 3.29/1.49  tff(c_1099, plain, (![A_99]: (v2_compts_1(k3_xboole_0('#skF_3', A_99), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_99), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_18, c_953])).
% 3.29/1.49  tff(c_1119, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_306, c_1099])).
% 3.29/1.49  tff(c_1146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_1119])).
% 3.29/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.49  
% 3.29/1.49  Inference rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Ref     : 0
% 3.29/1.49  #Sup     : 233
% 3.29/1.49  #Fact    : 0
% 3.29/1.49  #Define  : 0
% 3.29/1.49  #Split   : 0
% 3.29/1.49  #Chain   : 0
% 3.29/1.49  #Close   : 0
% 3.29/1.49  
% 3.29/1.49  Ordering : KBO
% 3.29/1.49  
% 3.29/1.49  Simplification rules
% 3.29/1.49  ----------------------
% 3.29/1.49  #Subsume      : 17
% 3.29/1.49  #Demod        : 229
% 3.29/1.49  #Tautology    : 75
% 3.29/1.49  #SimpNegUnit  : 4
% 3.29/1.49  #BackRed      : 1
% 3.29/1.49  
% 3.29/1.49  #Partial instantiations: 0
% 3.29/1.49  #Strategies tried      : 1
% 3.29/1.49  
% 3.29/1.49  Timing (in seconds)
% 3.29/1.49  ----------------------
% 3.29/1.50  Preprocessing        : 0.31
% 3.29/1.50  Parsing              : 0.17
% 3.29/1.50  CNF conversion       : 0.02
% 3.29/1.50  Main loop            : 0.43
% 3.29/1.50  Inferencing          : 0.14
% 3.29/1.50  Reduction            : 0.18
% 3.29/1.50  Demodulation         : 0.15
% 3.29/1.50  BG Simplification    : 0.02
% 3.29/1.50  Subsumption          : 0.06
% 3.29/1.50  Abstraction          : 0.02
% 3.29/1.50  MUC search           : 0.00
% 3.29/1.50  Cooper               : 0.00
% 3.29/1.50  Total                : 0.77
% 3.29/1.50  Index Insertion      : 0.00
% 3.29/1.50  Index Deletion       : 0.00
% 3.29/1.50  Index Matching       : 0.00
% 3.29/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------

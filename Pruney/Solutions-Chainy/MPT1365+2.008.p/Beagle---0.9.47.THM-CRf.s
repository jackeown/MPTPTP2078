%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:55 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 106 expanded)
%              Number of leaves         :   25 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 334 expanded)
%              Number of equality atoms :    6 (  13 expanded)
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

tff(f_107,negated_conjecture,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_88,axiom,(
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

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_83,plain,(
    ! [A_41,B_42,C_43] :
      ( k9_subset_1(A_41,B_42,C_43) = k3_xboole_0(B_42,C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_3') = k3_xboole_0(B_42,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_18,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_90,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_18])).

tff(c_91,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_32,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_24,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_20,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_233,plain,(
    ! [B_57,A_58] :
      ( v4_pre_topc(B_57,A_58)
      | ~ v2_compts_1(B_57,A_58)
      | ~ v8_pre_topc(A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_252,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_233])).

tff(c_271,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_20,c_252])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_22,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_255,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_233])).

tff(c_274,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_24,c_22,c_255])).

tff(c_89,plain,(
    ! [B_42] : k9_subset_1(u1_struct_0('#skF_1'),B_42,'#skF_2') = k3_xboole_0(B_42,'#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_83])).

tff(c_618,plain,(
    ! [A_81,B_82,C_83] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_81),B_82,C_83),A_81)
      | ~ v4_pre_topc(C_83,A_81)
      | ~ v4_pre_topc(B_82,A_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_633,plain,(
    ! [B_42] :
      ( v4_pre_topc(k3_xboole_0(B_42,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc('#skF_2','#skF_1')
      | ~ v4_pre_topc(B_42,'#skF_1')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_618])).

tff(c_684,plain,(
    ! [B_86] :
      ( v4_pre_topc(k3_xboole_0(B_86,'#skF_2'),'#skF_1')
      | ~ v4_pre_topc(B_86,'#skF_1')
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_28,c_274,c_633])).

tff(c_727,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1')
    | ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_684])).

tff(c_759,plain,(
    v4_pre_topc(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_727])).

tff(c_101,plain,(
    ! [A_45,B_46,C_47] :
      ( m1_subset_1(k9_subset_1(A_45,B_46,C_47),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_106,plain,(
    ! [B_42] :
      ( m1_subset_1(k3_xboole_0(B_42,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_101])).

tff(c_110,plain,(
    ! [B_48] : m1_subset_1(k3_xboole_0(B_48,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_106])).

tff(c_116,plain,(
    ! [A_1] : m1_subset_1(k3_xboole_0('#skF_3',A_1),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_441,plain,(
    ! [C_68,A_69,B_70] :
      ( v2_compts_1(C_68,A_69)
      | ~ v4_pre_topc(C_68,A_69)
      | ~ r1_tarski(C_68,B_70)
      | ~ v2_compts_1(B_70,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1541,plain,(
    ! [A_123,B_124,A_125] :
      ( v2_compts_1(k3_xboole_0(A_123,B_124),A_125)
      | ~ v4_pre_topc(k3_xboole_0(A_123,B_124),A_125)
      | ~ v2_compts_1(A_123,A_125)
      | ~ m1_subset_1(k3_xboole_0(A_123,B_124),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_subset_1(A_123,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_4,c_441])).

tff(c_1580,plain,(
    ! [A_1] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_1),'#skF_1')
      | ~ v2_compts_1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_116,c_1541])).

tff(c_1689,plain,(
    ! [A_127] :
      ( v2_compts_1(k3_xboole_0('#skF_3',A_127),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0('#skF_3',A_127),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26,c_20,c_1580])).

tff(c_1723,plain,(
    v2_compts_1(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_759,c_1689])).

tff(c_1747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_1723])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:06:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.68  
% 3.61/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.68  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > v8_pre_topc > v2_pre_topc > l1_pre_topc > k9_subset_1 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.61/1.68  
% 3.61/1.68  %Foreground sorts:
% 3.61/1.68  
% 3.61/1.68  
% 3.61/1.68  %Background operators:
% 3.61/1.68  
% 3.61/1.68  
% 3.61/1.68  %Foreground operators:
% 3.61/1.68  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.61/1.68  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 3.61/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.61/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.68  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.68  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.68  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.68  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.61/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.61/1.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.61/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.61/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.68  
% 3.61/1.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.61/1.69  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_compts_1)).
% 3.61/1.69  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.61/1.69  tff(f_70, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_compts_1)).
% 3.61/1.69  tff(f_57, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tops_1)).
% 3.61/1.69  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.61/1.69  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.61/1.69  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_compts_1)).
% 3.61/1.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.61/1.69  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_83, plain, (![A_41, B_42, C_43]: (k9_subset_1(A_41, B_42, C_43)=k3_xboole_0(B_42, C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.61/1.69  tff(c_88, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_3')=k3_xboole_0(B_42, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_83])).
% 3.61/1.69  tff(c_18, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_90, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_18])).
% 3.61/1.69  tff(c_91, plain, (~v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_90])).
% 3.61/1.69  tff(c_32, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_24, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_20, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_233, plain, (![B_57, A_58]: (v4_pre_topc(B_57, A_58) | ~v2_compts_1(B_57, A_58) | ~v8_pre_topc(A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.61/1.69  tff(c_252, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_233])).
% 3.61/1.69  tff(c_271, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_20, c_252])).
% 3.61/1.69  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_22, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.61/1.69  tff(c_255, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_233])).
% 3.61/1.69  tff(c_274, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_24, c_22, c_255])).
% 3.61/1.69  tff(c_89, plain, (![B_42]: (k9_subset_1(u1_struct_0('#skF_1'), B_42, '#skF_2')=k3_xboole_0(B_42, '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_83])).
% 3.61/1.69  tff(c_618, plain, (![A_81, B_82, C_83]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_81), B_82, C_83), A_81) | ~v4_pre_topc(C_83, A_81) | ~v4_pre_topc(B_82, A_81) | ~m1_subset_1(C_83, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.61/1.69  tff(c_633, plain, (![B_42]: (v4_pre_topc(k3_xboole_0(B_42, '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v4_pre_topc(B_42, '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_618])).
% 3.61/1.69  tff(c_684, plain, (![B_86]: (v4_pre_topc(k3_xboole_0(B_86, '#skF_2'), '#skF_1') | ~v4_pre_topc(B_86, '#skF_1') | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_28, c_274, c_633])).
% 3.61/1.69  tff(c_727, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_684])).
% 3.61/1.69  tff(c_759, plain, (v4_pre_topc(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_727])).
% 3.61/1.69  tff(c_101, plain, (![A_45, B_46, C_47]: (m1_subset_1(k9_subset_1(A_45, B_46, C_47), k1_zfmisc_1(A_45)) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.61/1.69  tff(c_106, plain, (![B_42]: (m1_subset_1(k3_xboole_0(B_42, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_88, c_101])).
% 3.61/1.69  tff(c_110, plain, (![B_48]: (m1_subset_1(k3_xboole_0(B_48, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_106])).
% 3.61/1.69  tff(c_116, plain, (![A_1]: (m1_subset_1(k3_xboole_0('#skF_3', A_1), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_110])).
% 3.61/1.69  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.61/1.69  tff(c_441, plain, (![C_68, A_69, B_70]: (v2_compts_1(C_68, A_69) | ~v4_pre_topc(C_68, A_69) | ~r1_tarski(C_68, B_70) | ~v2_compts_1(B_70, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.61/1.69  tff(c_1541, plain, (![A_123, B_124, A_125]: (v2_compts_1(k3_xboole_0(A_123, B_124), A_125) | ~v4_pre_topc(k3_xboole_0(A_123, B_124), A_125) | ~v2_compts_1(A_123, A_125) | ~m1_subset_1(k3_xboole_0(A_123, B_124), k1_zfmisc_1(u1_struct_0(A_125))) | ~m1_subset_1(A_123, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125))), inference(resolution, [status(thm)], [c_4, c_441])).
% 3.61/1.69  tff(c_1580, plain, (![A_1]: (v2_compts_1(k3_xboole_0('#skF_3', A_1), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_1), '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_116, c_1541])).
% 3.61/1.69  tff(c_1689, plain, (![A_127]: (v2_compts_1(k3_xboole_0('#skF_3', A_127), '#skF_1') | ~v4_pre_topc(k3_xboole_0('#skF_3', A_127), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26, c_20, c_1580])).
% 3.61/1.69  tff(c_1723, plain, (v2_compts_1(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_759, c_1689])).
% 3.61/1.69  tff(c_1747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_1723])).
% 3.61/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.69  
% 3.61/1.69  Inference rules
% 3.61/1.69  ----------------------
% 3.61/1.69  #Ref     : 0
% 3.61/1.69  #Sup     : 383
% 3.61/1.69  #Fact    : 0
% 3.61/1.69  #Define  : 0
% 3.61/1.69  #Split   : 0
% 3.61/1.69  #Chain   : 0
% 3.61/1.69  #Close   : 0
% 3.61/1.69  
% 3.61/1.69  Ordering : KBO
% 3.61/1.69  
% 3.61/1.69  Simplification rules
% 3.61/1.69  ----------------------
% 3.61/1.69  #Subsume      : 36
% 3.61/1.69  #Demod        : 316
% 3.61/1.69  #Tautology    : 132
% 3.61/1.69  #SimpNegUnit  : 5
% 3.61/1.69  #BackRed      : 1
% 3.61/1.69  
% 3.61/1.69  #Partial instantiations: 0
% 3.61/1.69  #Strategies tried      : 1
% 3.61/1.69  
% 3.61/1.69  Timing (in seconds)
% 3.61/1.69  ----------------------
% 3.61/1.69  Preprocessing        : 0.33
% 3.61/1.69  Parsing              : 0.18
% 3.61/1.69  CNF conversion       : 0.02
% 3.61/1.69  Main loop            : 0.53
% 3.61/1.69  Inferencing          : 0.17
% 3.61/1.69  Reduction            : 0.23
% 3.61/1.69  Demodulation         : 0.19
% 3.61/1.69  BG Simplification    : 0.03
% 3.61/1.69  Subsumption          : 0.08
% 3.61/1.69  Abstraction          : 0.03
% 3.61/1.69  MUC search           : 0.00
% 3.61/1.70  Cooper               : 0.00
% 3.61/1.70  Total                : 0.90
% 3.61/1.70  Index Insertion      : 0.00
% 3.61/1.70  Index Deletion       : 0.00
% 3.61/1.70  Index Matching       : 0.00
% 3.61/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------

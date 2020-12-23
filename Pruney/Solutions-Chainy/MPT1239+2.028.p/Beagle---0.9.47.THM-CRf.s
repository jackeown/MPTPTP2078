%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:44 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 111 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 215 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_464,plain,(
    ! [A_91,B_92,C_93] :
      ( k7_subset_1(A_91,B_92,C_93) = k4_xboole_0(B_92,C_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_475,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_94) = k4_xboole_0('#skF_2',C_94) ),
    inference(resolution,[status(thm)],[c_32,c_464])).

tff(c_18,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k7_subset_1(A_15,B_16,C_17),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_481,plain,(
    ! [C_94] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_94),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_18])).

tff(c_487,plain,(
    ! [C_94] : m1_subset_1(k4_xboole_0('#skF_2',C_94),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_481])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_26,B_30,C_32] :
      ( r1_tarski(k1_tops_1(A_26,B_30),k1_tops_1(A_26,C_32))
      | ~ r1_tarski(B_30,C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_532,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k1_tops_1(A_98,B_99),B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_536,plain,(
    ! [C_94] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_94)),k4_xboole_0('#skF_2',C_94))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_487,c_532])).

tff(c_1142,plain,(
    ! [C_136] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_136)),k4_xboole_0('#skF_2',C_136)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_536])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1230,plain,(
    ! [C_140] : r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_140)),C_140) ),
    inference(resolution,[status(thm)],[c_1142,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1250,plain,(
    ! [C_141] : r1_xboole_0(C_141,k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_141))) ),
    inference(resolution,[status(thm)],[c_1230,c_2])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1301,plain,(
    ! [C_146] : k4_xboole_0(C_146,k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_146))) = C_146 ),
    inference(resolution,[status(thm)],[c_1250,c_12])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_503,plain,(
    ! [C_96] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_3',C_96) = k4_xboole_0('#skF_3',C_96) ),
    inference(resolution,[status(thm)],[c_30,c_464])).

tff(c_509,plain,(
    ! [C_96] :
      ( m1_subset_1(k4_xboole_0('#skF_3',C_96),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_18])).

tff(c_515,plain,(
    ! [C_96] : m1_subset_1(k4_xboole_0('#skF_3',C_96),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_509])).

tff(c_534,plain,(
    ! [C_96] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_3',C_96)),k4_xboole_0('#skF_3',C_96))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_515,c_532])).

tff(c_754,plain,(
    ! [C_118] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_3',C_118)),k4_xboole_0('#skF_3',C_118)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_534])).

tff(c_805,plain,(
    ! [C_122] : r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_3',C_122)),C_122) ),
    inference(resolution,[status(thm)],[c_754,c_4])).

tff(c_820,plain,(
    ! [C_122] : r1_xboole_0(C_122,k1_tops_1('#skF_1',k4_xboole_0('#skF_3',C_122))) ),
    inference(resolution,[status(thm)],[c_805,c_2])).

tff(c_1355,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1301,c_820])).

tff(c_16,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_tarski(A_12,k4_xboole_0(B_13,C_14))
      | ~ r1_xboole_0(A_12,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_787,plain,(
    ! [A_119,B_120] :
      ( m1_subset_1(k1_tops_1(A_119,B_120),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( k7_subset_1(A_18,B_19,C_20) = k4_xboole_0(B_19,C_20)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2467,plain,(
    ! [A_182,B_183,C_184] :
      ( k7_subset_1(u1_struct_0(A_182),k1_tops_1(A_182,B_183),C_184) = k4_xboole_0(k1_tops_1(A_182,B_183),C_184)
      | ~ m1_subset_1(B_183,k1_zfmisc_1(u1_struct_0(A_182)))
      | ~ l1_pre_topc(A_182) ) ),
    inference(resolution,[status(thm)],[c_787,c_20])).

tff(c_2482,plain,(
    ! [C_184] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_184) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_184)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_2467])).

tff(c_2501,plain,(
    ! [C_184] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_184) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_184) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2482])).

tff(c_472,plain,(
    ! [C_93] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_93) = k4_xboole_0('#skF_2',C_93) ),
    inference(resolution,[status(thm)],[c_32,c_464])).

tff(c_28,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_474,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_28])).

tff(c_2814,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2501,c_474])).

tff(c_3422,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_2814])).

tff(c_3425,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1355,c_3422])).

tff(c_3486,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_3425])).

tff(c_3490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_487,c_32,c_8,c_3486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.73/1.85  
% 4.73/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.73/1.85  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.73/1.85  
% 4.73/1.85  %Foreground sorts:
% 4.73/1.85  
% 4.73/1.85  
% 4.73/1.85  %Background operators:
% 4.73/1.85  
% 4.73/1.85  
% 4.73/1.85  %Foreground operators:
% 4.73/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.73/1.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.73/1.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.73/1.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.73/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.73/1.85  tff('#skF_2', type, '#skF_2': $i).
% 4.73/1.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.73/1.85  tff('#skF_3', type, '#skF_3': $i).
% 4.73/1.85  tff('#skF_1', type, '#skF_1': $i).
% 4.73/1.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.73/1.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.73/1.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.85  
% 4.73/1.87  tff(f_95, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_tops_1)).
% 4.73/1.87  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.73/1.87  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.73/1.87  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.73/1.87  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 4.73/1.87  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 4.73/1.87  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.73/1.87  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.73/1.87  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.73/1.87  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.73/1.87  tff(f_63, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 4.73/1.87  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.73/1.87  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.73/1.87  tff(c_464, plain, (![A_91, B_92, C_93]: (k7_subset_1(A_91, B_92, C_93)=k4_xboole_0(B_92, C_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.73/1.87  tff(c_475, plain, (![C_94]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_94)=k4_xboole_0('#skF_2', C_94))), inference(resolution, [status(thm)], [c_32, c_464])).
% 4.73/1.87  tff(c_18, plain, (![A_15, B_16, C_17]: (m1_subset_1(k7_subset_1(A_15, B_16, C_17), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.73/1.87  tff(c_481, plain, (![C_94]: (m1_subset_1(k4_xboole_0('#skF_2', C_94), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_475, c_18])).
% 4.73/1.87  tff(c_487, plain, (![C_94]: (m1_subset_1(k4_xboole_0('#skF_2', C_94), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_481])).
% 4.73/1.87  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.73/1.87  tff(c_26, plain, (![A_26, B_30, C_32]: (r1_tarski(k1_tops_1(A_26, B_30), k1_tops_1(A_26, C_32)) | ~r1_tarski(B_30, C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.73/1.87  tff(c_532, plain, (![A_98, B_99]: (r1_tarski(k1_tops_1(A_98, B_99), B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.73/1.87  tff(c_536, plain, (![C_94]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_94)), k4_xboole_0('#skF_2', C_94)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_487, c_532])).
% 4.73/1.87  tff(c_1142, plain, (![C_136]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_136)), k4_xboole_0('#skF_2', C_136)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_536])).
% 4.73/1.87  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.73/1.87  tff(c_1230, plain, (![C_140]: (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_140)), C_140))), inference(resolution, [status(thm)], [c_1142, c_4])).
% 4.73/1.87  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.73/1.87  tff(c_1250, plain, (![C_141]: (r1_xboole_0(C_141, k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_141))))), inference(resolution, [status(thm)], [c_1230, c_2])).
% 4.73/1.87  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.73/1.87  tff(c_1301, plain, (![C_146]: (k4_xboole_0(C_146, k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_146)))=C_146)), inference(resolution, [status(thm)], [c_1250, c_12])).
% 4.73/1.87  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.73/1.87  tff(c_503, plain, (![C_96]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_3', C_96)=k4_xboole_0('#skF_3', C_96))), inference(resolution, [status(thm)], [c_30, c_464])).
% 4.73/1.87  tff(c_509, plain, (![C_96]: (m1_subset_1(k4_xboole_0('#skF_3', C_96), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_503, c_18])).
% 4.73/1.87  tff(c_515, plain, (![C_96]: (m1_subset_1(k4_xboole_0('#skF_3', C_96), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_509])).
% 4.73/1.87  tff(c_534, plain, (![C_96]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_3', C_96)), k4_xboole_0('#skF_3', C_96)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_515, c_532])).
% 4.73/1.87  tff(c_754, plain, (![C_118]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_3', C_118)), k4_xboole_0('#skF_3', C_118)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_534])).
% 4.73/1.87  tff(c_805, plain, (![C_122]: (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_3', C_122)), C_122))), inference(resolution, [status(thm)], [c_754, c_4])).
% 4.73/1.87  tff(c_820, plain, (![C_122]: (r1_xboole_0(C_122, k1_tops_1('#skF_1', k4_xboole_0('#skF_3', C_122))))), inference(resolution, [status(thm)], [c_805, c_2])).
% 4.73/1.87  tff(c_1355, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1301, c_820])).
% 4.73/1.87  tff(c_16, plain, (![A_12, B_13, C_14]: (r1_tarski(A_12, k4_xboole_0(B_13, C_14)) | ~r1_xboole_0(A_12, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.73/1.87  tff(c_787, plain, (![A_119, B_120]: (m1_subset_1(k1_tops_1(A_119, B_120), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.73/1.87  tff(c_20, plain, (![A_18, B_19, C_20]: (k7_subset_1(A_18, B_19, C_20)=k4_xboole_0(B_19, C_20) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.73/1.87  tff(c_2467, plain, (![A_182, B_183, C_184]: (k7_subset_1(u1_struct_0(A_182), k1_tops_1(A_182, B_183), C_184)=k4_xboole_0(k1_tops_1(A_182, B_183), C_184) | ~m1_subset_1(B_183, k1_zfmisc_1(u1_struct_0(A_182))) | ~l1_pre_topc(A_182))), inference(resolution, [status(thm)], [c_787, c_20])).
% 4.73/1.87  tff(c_2482, plain, (![C_184]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_184)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_184) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_2467])).
% 4.73/1.87  tff(c_2501, plain, (![C_184]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_184)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_184))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2482])).
% 4.73/1.87  tff(c_472, plain, (![C_93]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_93)=k4_xboole_0('#skF_2', C_93))), inference(resolution, [status(thm)], [c_32, c_464])).
% 4.73/1.87  tff(c_28, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.73/1.87  tff(c_474, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_472, c_28])).
% 4.73/1.87  tff(c_2814, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2501, c_474])).
% 4.73/1.87  tff(c_3422, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_2814])).
% 4.73/1.87  tff(c_3425, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1355, c_3422])).
% 4.73/1.87  tff(c_3486, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_3425])).
% 4.73/1.87  tff(c_3490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_487, c_32, c_8, c_3486])).
% 4.73/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.73/1.87  
% 4.73/1.87  Inference rules
% 4.73/1.87  ----------------------
% 4.73/1.87  #Ref     : 0
% 4.73/1.87  #Sup     : 808
% 4.73/1.87  #Fact    : 0
% 4.73/1.87  #Define  : 0
% 4.73/1.87  #Split   : 0
% 4.73/1.87  #Chain   : 0
% 4.73/1.87  #Close   : 0
% 4.73/1.87  
% 4.73/1.87  Ordering : KBO
% 4.73/1.87  
% 4.73/1.87  Simplification rules
% 4.73/1.87  ----------------------
% 4.73/1.87  #Subsume      : 16
% 4.73/1.87  #Demod        : 560
% 4.73/1.87  #Tautology    : 486
% 4.73/1.87  #SimpNegUnit  : 0
% 4.73/1.87  #BackRed      : 2
% 4.73/1.87  
% 4.73/1.87  #Partial instantiations: 0
% 4.73/1.87  #Strategies tried      : 1
% 4.73/1.87  
% 4.73/1.87  Timing (in seconds)
% 4.73/1.87  ----------------------
% 4.73/1.87  Preprocessing        : 0.32
% 4.73/1.87  Parsing              : 0.18
% 4.73/1.87  CNF conversion       : 0.02
% 4.73/1.87  Main loop            : 0.76
% 4.73/1.87  Inferencing          : 0.25
% 4.73/1.87  Reduction            : 0.29
% 4.73/1.87  Demodulation         : 0.23
% 4.73/1.87  BG Simplification    : 0.03
% 4.73/1.87  Subsumption          : 0.14
% 4.73/1.87  Abstraction          : 0.04
% 4.73/1.87  MUC search           : 0.00
% 4.73/1.87  Cooper               : 0.00
% 4.73/1.87  Total                : 1.12
% 4.73/1.87  Index Insertion      : 0.00
% 4.73/1.87  Index Deletion       : 0.00
% 4.73/1.87  Index Matching       : 0.00
% 4.73/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

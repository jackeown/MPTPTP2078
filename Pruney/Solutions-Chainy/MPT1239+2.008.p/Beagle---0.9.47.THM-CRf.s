%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:42 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.90s
% Verified   : 
% Statistics : Number of formulae       :   64 (  97 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   97 ( 190 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k1_tops_1(A,k7_subset_1(u1_struct_0(A),B,C)),k7_subset_1(u1_struct_0(A),k1_tops_1(A,B),k1_tops_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_696,plain,(
    ! [A_122,B_123,C_124] :
      ( k7_subset_1(A_122,B_123,C_124) = k4_xboole_0(B_123,C_124)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_707,plain,(
    ! [C_125] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_125) = k4_xboole_0('#skF_2',C_125) ),
    inference(resolution,[status(thm)],[c_38,c_696])).

tff(c_24,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k7_subset_1(A_16,B_17,C_18),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_713,plain,(
    ! [C_125] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_125),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_24])).

tff(c_719,plain,(
    ! [C_125] : m1_subset_1(k4_xboole_0('#skF_2',C_125),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_713])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_27,B_31,C_33] :
      ( r1_tarski(k1_tops_1(A_27,B_31),k1_tops_1(A_27,C_33))
      | ~ r1_tarski(B_31,C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1359,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(k1_tops_1(A_175,B_176),B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1372,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1359])).

tff(c_1388,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1372])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1402,plain,(
    k2_xboole_0(k1_tops_1('#skF_1','#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1388,c_12])).

tff(c_1365,plain,(
    ! [C_125] :
      ( r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_125)),k4_xboole_0('#skF_2',C_125))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_719,c_1359])).

tff(c_1563,plain,(
    ! [C_185] : r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_185)),k4_xboole_0('#skF_2',C_185)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1365])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1600,plain,(
    ! [C_187] : r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',C_187)),C_187) ),
    inference(resolution,[status(thm)],[c_1563,c_8])).

tff(c_20,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_xboole_0(A_10,B_11)
      | ~ r1_xboole_0(A_10,k2_xboole_0(B_11,C_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2748,plain,(
    ! [B_219,C_220] : r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2',k2_xboole_0(B_219,C_220))),B_219) ),
    inference(resolution,[status(thm)],[c_1600,c_20])).

tff(c_2771,plain,(
    r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1402,c_2748])).

tff(c_22,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(A_13,k4_xboole_0(B_14,C_15))
      | ~ r1_xboole_0(A_13,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1530,plain,(
    ! [A_181,B_182] :
      ( m1_subset_1(k1_tops_1(A_181,B_182),k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(u1_struct_0(A_181)))
      | ~ l1_pre_topc(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_19,B_20,C_21] :
      ( k7_subset_1(A_19,B_20,C_21) = k4_xboole_0(B_20,C_21)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4067,plain,(
    ! [A_268,B_269,C_270] :
      ( k7_subset_1(u1_struct_0(A_268),k1_tops_1(A_268,B_269),C_270) = k4_xboole_0(k1_tops_1(A_268,B_269),C_270)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268) ) ),
    inference(resolution,[status(thm)],[c_1530,c_26])).

tff(c_4082,plain,(
    ! [C_270] :
      ( k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_270) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_270)
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_4067])).

tff(c_4101,plain,(
    ! [C_270] : k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),C_270) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),C_270) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4082])).

tff(c_704,plain,(
    ! [C_124] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_124) = k4_xboole_0('#skF_2',C_124) ),
    inference(resolution,[status(thm)],[c_38,c_696])).

tff(c_34,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k7_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_706,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k7_subset_1(u1_struct_0('#skF_1'),k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_704,c_34])).

tff(c_4139,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4101,c_706])).

tff(c_5868,plain,
    ( ~ r1_xboole_0(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_22,c_4139])).

tff(c_5871,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')),k1_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2771,c_5868])).

tff(c_5874,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k4_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_5871])).

tff(c_5878,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_719,c_38,c_14,c_5874])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.88/2.13  
% 5.88/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.14  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k2_xboole_0 > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.90/2.14  
% 5.90/2.14  %Foreground sorts:
% 5.90/2.14  
% 5.90/2.14  
% 5.90/2.14  %Background operators:
% 5.90/2.14  
% 5.90/2.14  
% 5.90/2.14  %Foreground operators:
% 5.90/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.90/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.90/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.90/2.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.90/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.90/2.14  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.90/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.90/2.14  tff('#skF_1', type, '#skF_1': $i).
% 5.90/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.90/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.90/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.90/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.90/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.90/2.14  
% 5.90/2.15  tff(f_111, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, k7_subset_1(u1_struct_0(A), B, C)), k7_subset_1(u1_struct_0(A), k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_tops_1)).
% 5.90/2.15  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.90/2.15  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 5.90/2.15  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.90/2.15  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 5.90/2.15  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 5.90/2.15  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.90/2.15  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.90/2.15  tff(f_59, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 5.90/2.15  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 5.90/2.15  tff(f_79, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 5.90/2.15  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.90/2.15  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.90/2.15  tff(c_696, plain, (![A_122, B_123, C_124]: (k7_subset_1(A_122, B_123, C_124)=k4_xboole_0(B_123, C_124) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.90/2.15  tff(c_707, plain, (![C_125]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_125)=k4_xboole_0('#skF_2', C_125))), inference(resolution, [status(thm)], [c_38, c_696])).
% 5.90/2.15  tff(c_24, plain, (![A_16, B_17, C_18]: (m1_subset_1(k7_subset_1(A_16, B_17, C_18), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.90/2.15  tff(c_713, plain, (![C_125]: (m1_subset_1(k4_xboole_0('#skF_2', C_125), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_707, c_24])).
% 5.90/2.15  tff(c_719, plain, (![C_125]: (m1_subset_1(k4_xboole_0('#skF_2', C_125), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_713])).
% 5.90/2.15  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.90/2.15  tff(c_32, plain, (![A_27, B_31, C_33]: (r1_tarski(k1_tops_1(A_27, B_31), k1_tops_1(A_27, C_33)) | ~r1_tarski(B_31, C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_31, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.90/2.15  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.90/2.15  tff(c_1359, plain, (![A_175, B_176]: (r1_tarski(k1_tops_1(A_175, B_176), B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.90/2.15  tff(c_1372, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1359])).
% 5.90/2.15  tff(c_1388, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1372])).
% 5.90/2.15  tff(c_12, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.90/2.15  tff(c_1402, plain, (k2_xboole_0(k1_tops_1('#skF_1', '#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_1388, c_12])).
% 5.90/2.15  tff(c_1365, plain, (![C_125]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_125)), k4_xboole_0('#skF_2', C_125)) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_719, c_1359])).
% 5.90/2.15  tff(c_1563, plain, (![C_185]: (r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_185)), k4_xboole_0('#skF_2', C_185)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1365])).
% 5.90/2.15  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.90/2.15  tff(c_1600, plain, (![C_187]: (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', C_187)), C_187))), inference(resolution, [status(thm)], [c_1563, c_8])).
% 5.90/2.15  tff(c_20, plain, (![A_10, B_11, C_12]: (r1_xboole_0(A_10, B_11) | ~r1_xboole_0(A_10, k2_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.90/2.15  tff(c_2748, plain, (![B_219, C_220]: (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', k2_xboole_0(B_219, C_220))), B_219))), inference(resolution, [status(thm)], [c_1600, c_20])).
% 5.90/2.15  tff(c_2771, plain, (r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1402, c_2748])).
% 5.90/2.15  tff(c_22, plain, (![A_13, B_14, C_15]: (r1_tarski(A_13, k4_xboole_0(B_14, C_15)) | ~r1_xboole_0(A_13, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.90/2.15  tff(c_1530, plain, (![A_181, B_182]: (m1_subset_1(k1_tops_1(A_181, B_182), k1_zfmisc_1(u1_struct_0(A_181))) | ~m1_subset_1(B_182, k1_zfmisc_1(u1_struct_0(A_181))) | ~l1_pre_topc(A_181))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.90/2.15  tff(c_26, plain, (![A_19, B_20, C_21]: (k7_subset_1(A_19, B_20, C_21)=k4_xboole_0(B_20, C_21) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.90/2.15  tff(c_4067, plain, (![A_268, B_269, C_270]: (k7_subset_1(u1_struct_0(A_268), k1_tops_1(A_268, B_269), C_270)=k4_xboole_0(k1_tops_1(A_268, B_269), C_270) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(A_268))), inference(resolution, [status(thm)], [c_1530, c_26])).
% 5.90/2.15  tff(c_4082, plain, (![C_270]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_270)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_270) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_4067])).
% 5.90/2.15  tff(c_4101, plain, (![C_270]: (k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), C_270)=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), C_270))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4082])).
% 5.90/2.15  tff(c_704, plain, (![C_124]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_124)=k4_xboole_0('#skF_2', C_124))), inference(resolution, [status(thm)], [c_38, c_696])).
% 5.90/2.15  tff(c_34, plain, (~r1_tarski(k1_tops_1('#skF_1', k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 5.90/2.15  tff(c_706, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k7_subset_1(u1_struct_0('#skF_1'), k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_704, c_34])).
% 5.90/2.15  tff(c_4139, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4101, c_706])).
% 5.90/2.15  tff(c_5868, plain, (~r1_xboole_0(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_3')) | ~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_4139])).
% 5.90/2.15  tff(c_5871, plain, (~r1_tarski(k1_tops_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), k1_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2771, c_5868])).
% 5.90/2.15  tff(c_5874, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k4_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_5871])).
% 5.90/2.15  tff(c_5878, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_719, c_38, c_14, c_5874])).
% 5.90/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.90/2.15  
% 5.90/2.15  Inference rules
% 5.90/2.15  ----------------------
% 5.90/2.15  #Ref     : 0
% 5.90/2.15  #Sup     : 1382
% 5.90/2.15  #Fact    : 0
% 5.90/2.15  #Define  : 0
% 5.90/2.15  #Split   : 6
% 5.90/2.15  #Chain   : 0
% 5.90/2.15  #Close   : 0
% 5.90/2.15  
% 5.90/2.15  Ordering : KBO
% 5.90/2.15  
% 5.90/2.15  Simplification rules
% 5.90/2.15  ----------------------
% 5.90/2.15  #Subsume      : 83
% 5.90/2.15  #Demod        : 864
% 5.90/2.15  #Tautology    : 840
% 5.90/2.15  #SimpNegUnit  : 0
% 5.90/2.15  #BackRed      : 2
% 5.90/2.15  
% 5.90/2.15  #Partial instantiations: 0
% 5.90/2.15  #Strategies tried      : 1
% 5.90/2.15  
% 5.90/2.15  Timing (in seconds)
% 5.90/2.15  ----------------------
% 5.90/2.15  Preprocessing        : 0.29
% 5.90/2.15  Parsing              : 0.15
% 5.90/2.15  CNF conversion       : 0.02
% 5.90/2.15  Main loop            : 1.02
% 5.90/2.15  Inferencing          : 0.33
% 5.90/2.15  Reduction            : 0.40
% 5.90/2.15  Demodulation         : 0.32
% 5.90/2.15  BG Simplification    : 0.03
% 5.90/2.15  Subsumption          : 0.20
% 5.90/2.15  Abstraction          : 0.06
% 5.90/2.15  MUC search           : 0.00
% 5.90/2.15  Cooper               : 0.00
% 5.90/2.15  Total                : 1.34
% 5.90/2.15  Index Insertion      : 0.00
% 5.90/2.15  Index Deletion       : 0.00
% 5.90/2.16  Index Matching       : 0.00
% 5.90/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

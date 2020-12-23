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
% DateTime   : Thu Dec  3 10:19:04 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 136 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 241 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_87,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    ! [B_60] : k9_subset_1(u1_struct_0('#skF_1'),B_60,'#skF_3') = k3_xboole_0(B_60,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k9_subset_1(A_11,B_12,C_13),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [B_60] :
      ( m1_subset_1(k3_xboole_0(B_60,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_12])).

tff(c_139,plain,(
    ! [B_60] : m1_subset_1(k3_xboole_0(B_60,'#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_133])).

tff(c_8,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_10] : m1_subset_1(k2_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_33,plain,(
    ! [A_10] : m1_subset_1(A_10,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_103,plain,(
    ! [A_54,B_55] : k9_subset_1(A_54,B_55,A_54) = k3_xboole_0(B_55,A_54) ),
    inference(resolution,[status(thm)],[c_33,c_87])).

tff(c_109,plain,(
    ! [B_55,A_54] :
      ( m1_subset_1(k3_xboole_0(B_55,A_54),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(A_54,k1_zfmisc_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_12])).

tff(c_117,plain,(
    ! [B_56,A_57] : m1_subset_1(k3_xboole_0(B_56,A_57),k1_zfmisc_1(A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_109])).

tff(c_18,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    ! [B_56,A_57] : r1_tarski(k3_xboole_0(B_56,A_57),A_57) ),
    inference(resolution,[status(thm)],[c_117,c_18])).

tff(c_24,plain,(
    ! [A_23,B_27,C_29] :
      ( r1_tarski(k2_pre_topc(A_23,B_27),k2_pre_topc(A_23,C_29))
      | ~ r1_tarski(B_27,C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [A_10] : r1_tarski(A_10,A_10) ),
    inference(resolution,[status(thm)],[c_33,c_44])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(A_4,k3_xboole_0(B_5,C_6))
      | ~ r1_tarski(A_4,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_277,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(k2_pre_topc(A_88,B_89),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( k9_subset_1(A_14,B_15,C_16) = k3_xboole_0(B_15,C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_791,plain,(
    ! [A_166,B_167,B_168] :
      ( k9_subset_1(u1_struct_0(A_166),B_167,k2_pre_topc(A_166,B_168)) = k3_xboole_0(B_167,k2_pre_topc(A_166,B_168))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(resolution,[status(thm)],[c_277,c_14])).

tff(c_825,plain,(
    ! [B_167] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_167,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_167,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_791])).

tff(c_858,plain,(
    ! [B_167] : k9_subset_1(u1_struct_0('#skF_1'),B_167,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_167,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_825])).

tff(c_100,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_87])).

tff(c_26,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_126,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_26])).

tff(c_863,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_126])).

tff(c_917,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_863])).

tff(c_1231,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_917])).

tff(c_1234,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1231])).

tff(c_1237,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_139,c_30,c_1234])).

tff(c_1240,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_1237])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1240])).

tff(c_1245,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_917])).

tff(c_1249,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1245])).

tff(c_1253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_139,c_28,c_124,c_1249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:15:35 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.59  
% 3.39/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k1_enumset1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 3.39/1.60  
% 3.39/1.60  %Foreground sorts:
% 3.39/1.60  
% 3.39/1.60  
% 3.39/1.60  %Background operators:
% 3.39/1.60  
% 3.39/1.60  
% 3.39/1.60  %Foreground operators:
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.39/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.39/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.39/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.39/1.60  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.39/1.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.39/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.39/1.60  
% 3.39/1.61  tff(f_84, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_pre_topc)).
% 3.39/1.61  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.39/1.61  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 3.39/1.61  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.39/1.61  tff(f_41, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.39/1.61  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.61  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_pre_topc)).
% 3.39/1.61  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 3.39/1.61  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.39/1.61  tff(f_61, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 3.39/1.61  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.39/1.61  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.39/1.61  tff(c_87, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.61  tff(c_127, plain, (![B_60]: (k9_subset_1(u1_struct_0('#skF_1'), B_60, '#skF_3')=k3_xboole_0(B_60, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_87])).
% 3.39/1.61  tff(c_12, plain, (![A_11, B_12, C_13]: (m1_subset_1(k9_subset_1(A_11, B_12, C_13), k1_zfmisc_1(A_11)) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.39/1.61  tff(c_133, plain, (![B_60]: (m1_subset_1(k3_xboole_0(B_60, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_127, c_12])).
% 3.39/1.61  tff(c_139, plain, (![B_60]: (m1_subset_1(k3_xboole_0(B_60, '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_133])).
% 3.39/1.61  tff(c_8, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.39/1.61  tff(c_10, plain, (![A_10]: (m1_subset_1(k2_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.39/1.61  tff(c_33, plain, (![A_10]: (m1_subset_1(A_10, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 3.39/1.61  tff(c_103, plain, (![A_54, B_55]: (k9_subset_1(A_54, B_55, A_54)=k3_xboole_0(B_55, A_54))), inference(resolution, [status(thm)], [c_33, c_87])).
% 3.39/1.61  tff(c_109, plain, (![B_55, A_54]: (m1_subset_1(k3_xboole_0(B_55, A_54), k1_zfmisc_1(A_54)) | ~m1_subset_1(A_54, k1_zfmisc_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_12])).
% 3.39/1.61  tff(c_117, plain, (![B_56, A_57]: (m1_subset_1(k3_xboole_0(B_56, A_57), k1_zfmisc_1(A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_33, c_109])).
% 3.39/1.61  tff(c_18, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.61  tff(c_124, plain, (![B_56, A_57]: (r1_tarski(k3_xboole_0(B_56, A_57), A_57))), inference(resolution, [status(thm)], [c_117, c_18])).
% 3.39/1.61  tff(c_24, plain, (![A_23, B_27, C_29]: (r1_tarski(k2_pre_topc(A_23, B_27), k2_pre_topc(A_23, C_29)) | ~r1_tarski(B_27, C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.39/1.61  tff(c_44, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.61  tff(c_56, plain, (![A_10]: (r1_tarski(A_10, A_10))), inference(resolution, [status(thm)], [c_33, c_44])).
% 3.39/1.61  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.61  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.39/1.61  tff(c_4, plain, (![A_4, B_5, C_6]: (r1_tarski(A_4, k3_xboole_0(B_5, C_6)) | ~r1_tarski(A_4, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.61  tff(c_277, plain, (![A_88, B_89]: (m1_subset_1(k2_pre_topc(A_88, B_89), k1_zfmisc_1(u1_struct_0(A_88))) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.39/1.61  tff(c_14, plain, (![A_14, B_15, C_16]: (k9_subset_1(A_14, B_15, C_16)=k3_xboole_0(B_15, C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.39/1.61  tff(c_791, plain, (![A_166, B_167, B_168]: (k9_subset_1(u1_struct_0(A_166), B_167, k2_pre_topc(A_166, B_168))=k3_xboole_0(B_167, k2_pre_topc(A_166, B_168)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(resolution, [status(thm)], [c_277, c_14])).
% 3.39/1.61  tff(c_825, plain, (![B_167]: (k9_subset_1(u1_struct_0('#skF_1'), B_167, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_167, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_791])).
% 3.39/1.61  tff(c_858, plain, (![B_167]: (k9_subset_1(u1_struct_0('#skF_1'), B_167, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_167, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_825])).
% 3.39/1.61  tff(c_100, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_87])).
% 3.39/1.61  tff(c_26, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.39/1.61  tff(c_126, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_26])).
% 3.39/1.61  tff(c_863, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_858, c_126])).
% 3.39/1.61  tff(c_917, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_863])).
% 3.39/1.61  tff(c_1231, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_917])).
% 3.39/1.61  tff(c_1234, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1231])).
% 3.39/1.61  tff(c_1237, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_139, c_30, c_1234])).
% 3.39/1.61  tff(c_1240, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_1237])).
% 3.39/1.61  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_1240])).
% 3.39/1.61  tff(c_1245, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_917])).
% 3.39/1.61  tff(c_1249, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1245])).
% 3.39/1.61  tff(c_1253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_139, c_28, c_124, c_1249])).
% 3.39/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.61  
% 3.39/1.61  Inference rules
% 3.39/1.61  ----------------------
% 3.39/1.61  #Ref     : 0
% 3.39/1.61  #Sup     : 272
% 3.39/1.61  #Fact    : 0
% 3.39/1.61  #Define  : 0
% 3.39/1.61  #Split   : 3
% 3.39/1.61  #Chain   : 0
% 3.39/1.61  #Close   : 0
% 3.39/1.61  
% 3.39/1.61  Ordering : KBO
% 3.39/1.61  
% 3.39/1.61  Simplification rules
% 3.39/1.61  ----------------------
% 3.39/1.61  #Subsume      : 2
% 3.39/1.61  #Demod        : 192
% 3.39/1.61  #Tautology    : 123
% 3.39/1.61  #SimpNegUnit  : 0
% 3.39/1.61  #BackRed      : 2
% 3.39/1.61  
% 3.39/1.61  #Partial instantiations: 0
% 3.39/1.61  #Strategies tried      : 1
% 3.39/1.61  
% 3.39/1.61  Timing (in seconds)
% 3.39/1.61  ----------------------
% 3.39/1.61  Preprocessing        : 0.31
% 3.39/1.61  Parsing              : 0.17
% 3.39/1.61  CNF conversion       : 0.02
% 3.39/1.61  Main loop            : 0.53
% 3.39/1.61  Inferencing          : 0.19
% 3.39/1.61  Reduction            : 0.18
% 3.39/1.61  Demodulation         : 0.14
% 3.39/1.61  BG Simplification    : 0.03
% 3.39/1.61  Subsumption          : 0.10
% 3.39/1.61  Abstraction          : 0.04
% 3.39/1.61  MUC search           : 0.00
% 3.39/1.61  Cooper               : 0.00
% 3.39/1.62  Total                : 0.87
% 3.39/1.62  Index Insertion      : 0.00
% 3.39/1.62  Index Deletion       : 0.00
% 3.39/1.62  Index Matching       : 0.00
% 3.39/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

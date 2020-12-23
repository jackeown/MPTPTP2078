%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:04 EST 2020

% Result     : Theorem 18.14s
% Output     : CNFRefutation 18.14s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 182 expanded)
%              Number of leaves         :   25 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  114 ( 327 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_63,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_71,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_63])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_39,B_40] : r1_tarski(k3_xboole_0(A_39,B_40),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_8])).

tff(c_253,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1913,plain,(
    ! [A_197,B_198,C_199,A_200] :
      ( r1_tarski(A_197,k3_xboole_0(B_198,C_199))
      | ~ r1_tarski(A_197,A_200)
      | ~ r1_tarski(A_200,C_199)
      | ~ r1_tarski(A_200,B_198) ) ),
    inference(resolution,[status(thm)],[c_253,c_6])).

tff(c_3431,plain,(
    ! [A_267,B_268,B_269,C_270] :
      ( r1_tarski(k3_xboole_0(A_267,B_268),k3_xboole_0(B_269,C_270))
      | ~ r1_tarski(A_267,C_270)
      | ~ r1_tarski(A_267,B_269) ) ),
    inference(resolution,[status(thm)],[c_86,c_1913])).

tff(c_10,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_112,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(B_47,C_46)
      | ~ r1_tarski(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_146,plain,(
    ! [A_53,A_54,B_55] :
      ( r1_tarski(A_53,A_54)
      | ~ r1_tarski(A_53,k4_xboole_0(A_54,B_55)) ) ),
    inference(resolution,[status(thm)],[c_8,c_112])).

tff(c_157,plain,(
    ! [A_53,A_11,B_12] :
      ( r1_tarski(A_53,A_11)
      | ~ r1_tarski(A_53,k3_xboole_0(A_11,B_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_146])).

tff(c_9292,plain,(
    ! [A_365,B_366,B_367,C_368] :
      ( r1_tarski(k3_xboole_0(A_365,B_366),B_367)
      | ~ r1_tarski(A_365,C_368)
      | ~ r1_tarski(A_365,B_367) ) ),
    inference(resolution,[status(thm)],[c_3431,c_157])).

tff(c_9479,plain,(
    ! [B_369,B_370] :
      ( r1_tarski(k3_xboole_0('#skF_2',B_369),B_370)
      | ~ r1_tarski('#skF_2',B_370) ) ),
    inference(resolution,[status(thm)],[c_71,c_9292])).

tff(c_9559,plain,(
    ! [B_2,B_370] :
      ( r1_tarski(k3_xboole_0(B_2,'#skF_2'),B_370)
      | ~ r1_tarski('#skF_2',B_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_9479])).

tff(c_16,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_95,plain,(
    ! [A_41,B_42] : r1_tarski(k3_xboole_0(A_41,B_42),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_8])).

tff(c_98,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_95])).

tff(c_20,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_tarski(k2_pre_topc(A_20,B_24),k2_pre_topc(A_20,C_26))
      | ~ r1_tarski(B_24,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_372,plain,(
    ! [A_85,B_86] :
      ( m1_subset_1(k2_pre_topc(A_85,B_86),k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] :
      ( k9_subset_1(A_13,B_14,C_15) = k3_xboole_0(B_14,C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2227,plain,(
    ! [A_215,B_216,B_217] :
      ( k9_subset_1(u1_struct_0(A_215),B_216,k2_pre_topc(A_215,B_217)) = k3_xboole_0(B_216,k2_pre_topc(A_215,B_217))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(resolution,[status(thm)],[c_372,c_12])).

tff(c_2234,plain,(
    ! [B_216] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_216,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_216,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_24,c_2227])).

tff(c_2241,plain,(
    ! [B_216] : k9_subset_1(u1_struct_0('#skF_1'),B_216,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_216,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2234])).

tff(c_128,plain,(
    ! [A_48,B_49,C_50] :
      ( k9_subset_1(A_48,B_49,C_50) = k3_xboole_0(B_49,C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_136,plain,(
    ! [B_49] : k9_subset_1(u1_struct_0('#skF_1'),B_49,'#skF_3') = k3_xboole_0(B_49,'#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_128])).

tff(c_22,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_287,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_22])).

tff(c_288,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_287])).

tff(c_2247,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2241,c_288])).

tff(c_2248,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_3'),k2_pre_topc('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2247])).

tff(c_3409,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4,c_2248])).

tff(c_29389,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3409])).

tff(c_29547,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_29389])).

tff(c_29550,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_86,c_29547])).

tff(c_29554,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_29550])).

tff(c_29557,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_9559,c_29554])).

tff(c_29582,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_29557])).

tff(c_29583,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_3','#skF_2')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3409])).

tff(c_29825,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_29583])).

tff(c_29828,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_3','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_98,c_29825])).

tff(c_29832,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_29828])).

tff(c_29835,plain,(
    ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_9559,c_29832])).

tff(c_29860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_29835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.14/8.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.14/8.56  
% 18.14/8.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.14/8.56  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 18.14/8.56  
% 18.14/8.56  %Foreground sorts:
% 18.14/8.56  
% 18.14/8.56  
% 18.14/8.56  %Background operators:
% 18.14/8.56  
% 18.14/8.56  
% 18.14/8.56  %Foreground operators:
% 18.14/8.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.14/8.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.14/8.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.14/8.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.14/8.56  tff('#skF_2', type, '#skF_2': $i).
% 18.14/8.56  tff('#skF_3', type, '#skF_3': $i).
% 18.14/8.56  tff('#skF_1', type, '#skF_1': $i).
% 18.14/8.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.14/8.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.14/8.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.14/8.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.14/8.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.14/8.56  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 18.14/8.56  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 18.14/8.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.14/8.56  
% 18.14/8.58  tff(f_80, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 18.14/8.58  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 18.14/8.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.14/8.58  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.14/8.58  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 18.14/8.58  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 18.14/8.58  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 18.14/8.58  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 18.14/8.58  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 18.14/8.58  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 18.14/8.58  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.14/8.58  tff(c_63, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.14/8.58  tff(c_71, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_63])).
% 18.14/8.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.14/8.58  tff(c_77, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.14/8.58  tff(c_8, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.14/8.58  tff(c_86, plain, (![A_39, B_40]: (r1_tarski(k3_xboole_0(A_39, B_40), A_39))), inference(superposition, [status(thm), theory('equality')], [c_77, c_8])).
% 18.14/8.58  tff(c_253, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.14/8.58  tff(c_6, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.14/8.58  tff(c_1913, plain, (![A_197, B_198, C_199, A_200]: (r1_tarski(A_197, k3_xboole_0(B_198, C_199)) | ~r1_tarski(A_197, A_200) | ~r1_tarski(A_200, C_199) | ~r1_tarski(A_200, B_198))), inference(resolution, [status(thm)], [c_253, c_6])).
% 18.14/8.58  tff(c_3431, plain, (![A_267, B_268, B_269, C_270]: (r1_tarski(k3_xboole_0(A_267, B_268), k3_xboole_0(B_269, C_270)) | ~r1_tarski(A_267, C_270) | ~r1_tarski(A_267, B_269))), inference(resolution, [status(thm)], [c_86, c_1913])).
% 18.14/8.58  tff(c_10, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.14/8.58  tff(c_112, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(B_47, C_46) | ~r1_tarski(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.14/8.58  tff(c_146, plain, (![A_53, A_54, B_55]: (r1_tarski(A_53, A_54) | ~r1_tarski(A_53, k4_xboole_0(A_54, B_55)))), inference(resolution, [status(thm)], [c_8, c_112])).
% 18.14/8.58  tff(c_157, plain, (![A_53, A_11, B_12]: (r1_tarski(A_53, A_11) | ~r1_tarski(A_53, k3_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_146])).
% 18.14/8.58  tff(c_9292, plain, (![A_365, B_366, B_367, C_368]: (r1_tarski(k3_xboole_0(A_365, B_366), B_367) | ~r1_tarski(A_365, C_368) | ~r1_tarski(A_365, B_367))), inference(resolution, [status(thm)], [c_3431, c_157])).
% 18.14/8.58  tff(c_9479, plain, (![B_369, B_370]: (r1_tarski(k3_xboole_0('#skF_2', B_369), B_370) | ~r1_tarski('#skF_2', B_370))), inference(resolution, [status(thm)], [c_71, c_9292])).
% 18.14/8.58  tff(c_9559, plain, (![B_2, B_370]: (r1_tarski(k3_xboole_0(B_2, '#skF_2'), B_370) | ~r1_tarski('#skF_2', B_370))), inference(superposition, [status(thm), theory('equality')], [c_2, c_9479])).
% 18.14/8.58  tff(c_16, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 18.14/8.58  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.14/8.58  tff(c_95, plain, (![A_41, B_42]: (r1_tarski(k3_xboole_0(A_41, B_42), A_41))), inference(superposition, [status(thm), theory('equality')], [c_77, c_8])).
% 18.14/8.58  tff(c_98, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_95])).
% 18.14/8.58  tff(c_20, plain, (![A_20, B_24, C_26]: (r1_tarski(k2_pre_topc(A_20, B_24), k2_pre_topc(A_20, C_26)) | ~r1_tarski(B_24, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 18.14/8.58  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.14/8.58  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.14/8.58  tff(c_372, plain, (![A_85, B_86]: (m1_subset_1(k2_pre_topc(A_85, B_86), k1_zfmisc_1(u1_struct_0(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.14/8.58  tff(c_12, plain, (![A_13, B_14, C_15]: (k9_subset_1(A_13, B_14, C_15)=k3_xboole_0(B_14, C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.14/8.58  tff(c_2227, plain, (![A_215, B_216, B_217]: (k9_subset_1(u1_struct_0(A_215), B_216, k2_pre_topc(A_215, B_217))=k3_xboole_0(B_216, k2_pre_topc(A_215, B_217)) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(resolution, [status(thm)], [c_372, c_12])).
% 18.14/8.58  tff(c_2234, plain, (![B_216]: (k9_subset_1(u1_struct_0('#skF_1'), B_216, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_216, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_2227])).
% 18.14/8.58  tff(c_2241, plain, (![B_216]: (k9_subset_1(u1_struct_0('#skF_1'), B_216, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_216, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2234])).
% 18.14/8.58  tff(c_128, plain, (![A_48, B_49, C_50]: (k9_subset_1(A_48, B_49, C_50)=k3_xboole_0(B_49, C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.14/8.58  tff(c_136, plain, (![B_49]: (k9_subset_1(u1_struct_0('#skF_1'), B_49, '#skF_3')=k3_xboole_0(B_49, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_128])).
% 18.14/8.58  tff(c_22, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 18.14/8.58  tff(c_287, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_22])).
% 18.14/8.58  tff(c_288, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_287])).
% 18.14/8.58  tff(c_2247, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2241, c_288])).
% 18.14/8.58  tff(c_2248, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_3'), k2_pre_topc('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2247])).
% 18.14/8.58  tff(c_3409, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_4, c_2248])).
% 18.14/8.58  tff(c_29389, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3409])).
% 18.14/8.58  tff(c_29547, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_29389])).
% 18.14/8.58  tff(c_29550, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_86, c_29547])).
% 18.14/8.58  tff(c_29554, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_29550])).
% 18.14/8.58  tff(c_29557, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_9559, c_29554])).
% 18.14/8.58  tff(c_29582, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_29557])).
% 18.14/8.58  tff(c_29583, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_3', '#skF_2')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_3409])).
% 18.14/8.58  tff(c_29825, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_29583])).
% 18.14/8.58  tff(c_29828, plain, (~m1_subset_1(k3_xboole_0('#skF_3', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_98, c_29825])).
% 18.14/8.58  tff(c_29832, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_29828])).
% 18.14/8.58  tff(c_29835, plain, (~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_9559, c_29832])).
% 18.14/8.58  tff(c_29860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_29835])).
% 18.14/8.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.14/8.58  
% 18.14/8.58  Inference rules
% 18.14/8.58  ----------------------
% 18.14/8.58  #Ref     : 0
% 18.14/8.58  #Sup     : 7684
% 18.14/8.58  #Fact    : 0
% 18.14/8.58  #Define  : 0
% 18.14/8.58  #Split   : 11
% 18.14/8.58  #Chain   : 0
% 18.14/8.58  #Close   : 0
% 18.14/8.58  
% 18.14/8.58  Ordering : KBO
% 18.14/8.58  
% 18.14/8.58  Simplification rules
% 18.14/8.58  ----------------------
% 18.14/8.58  #Subsume      : 1582
% 18.14/8.58  #Demod        : 1229
% 18.14/8.58  #Tautology    : 1167
% 18.14/8.58  #SimpNegUnit  : 0
% 18.14/8.58  #BackRed      : 2
% 18.14/8.58  
% 18.14/8.58  #Partial instantiations: 0
% 18.14/8.58  #Strategies tried      : 1
% 18.14/8.58  
% 18.14/8.58  Timing (in seconds)
% 18.14/8.58  ----------------------
% 18.43/8.58  Preprocessing        : 0.48
% 18.43/8.58  Parsing              : 0.25
% 18.43/8.58  CNF conversion       : 0.03
% 18.43/8.58  Main loop            : 7.19
% 18.43/8.58  Inferencing          : 1.19
% 18.43/8.58  Reduction            : 3.31
% 18.43/8.58  Demodulation         : 2.88
% 18.43/8.58  BG Simplification    : 0.16
% 18.43/8.58  Subsumption          : 2.06
% 18.43/8.58  Abstraction          : 0.19
% 18.43/8.58  MUC search           : 0.00
% 18.43/8.58  Cooper               : 0.00
% 18.43/8.58  Total                : 7.71
% 18.43/8.58  Index Insertion      : 0.00
% 18.43/8.58  Index Deletion       : 0.00
% 18.43/8.58  Index Matching       : 0.00
% 18.43/8.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
